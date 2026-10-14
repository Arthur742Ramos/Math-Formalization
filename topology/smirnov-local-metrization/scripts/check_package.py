"""Audit project pins, roles, bounds, proof closures and recorded source hashes."""
import argparse,hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[1]
TEAM=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
AXIOMS={'propext','Classical.choice','Quot.sound'}
def check(log,write):
    assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
    lock=json.loads((ROOT/'lake-manifest.json').read_text())
    assert lock['name']=='smirnovLocalMetrization'
    assert not any(p['name']=='nagataSmirnov' for p in lock['packages'])
    for name,rev in [('mathlib','065356127b1dc0016f66b7283ce0ce2c4055aa55')]:
        assert next(p for p in lock['packages'] if p['name']==name)['rev']==rev
    config=json.loads((ROOT/'comparator.json').read_text());assert set(config['permitted_axioms'])==AXIOMS
    workflows=ROOT.parents[1]/'.github/workflows'
    for name in ['palomar-smirnov.yml','palomar-smirnov-renderer.yml']:
        text=(workflows/name).read_text()
        assert '.github/workflows/'+name in text
        assert "branches: ['topology/smirnov-local-metrization']" in text
    request=re.search(r'^\s+request_id: (\S+)\s*$',(workflows/'palomar-smirnov.yml').read_text(),re.M)
    assert request and re.fullmatch(r'[0-9a-z]{12}',request.group(1))
    assert len(config['theorem_names'])==6
    assert config['challenge_module']=='SmirnovChallenge'
    assert config['solution_module']=='SmirnovSolution'
    challenge=(ROOT/'SmirnovChallenge.lean').read_text(encoding='utf-8')
    assert len(challenge.splitlines())<=1000 and len(challenge.encode())<=100*1024
    assert all(x.startswith('Mathlib.') for x in re.findall(r'^public import (\S+)$',challenge,re.M))
    metadata=json.loads((ROOT/'formalization.yaml').read_text(encoding='utf-8'))
    for field in ['authors','responsible_maintainers']: assert metadata['project'][field]==TEAM
    assert '@[expose] public section' in challenge
    assert 'SecondCountableTopology' not in challenge and 'SeparableSpace' not in challenge
    hashes={}
    for path in ROOT.rglob('*.lean'):
        if '.lake' in path.relative_to(ROOT).parts:continue
        text=path.read_text(encoding='utf-8')
        assert re.search(r'^module\s*$',text,re.M),str(path)
        assert not re.search(r'\b(sorry|admit|axiom)\b',text),str(path)
        assert len(text.splitlines())<=10000
        hashes[path.relative_to(ROOT).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    support=json.loads((ROOT/'verification/registered-support-provenance.json').read_text())
    assert len(support)==4
    for name,record in support.items():
        assert record['source_commit']=='6aa68b2cb67719a187e64de29567443575eb560e'
        assert hashes[name]==record['adapted_sha256']
    if log:
        reports=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",pathlib.Path(log).read_text(encoding='utf-8-sig')))
        assert len(reports)==10,len(reports)
        for name in config['theorem_names']:assert name in reports,name
        assert all({s.strip() for s in a.split(',') if s.strip()}<=AXIOMS for a in reports.values())
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json','formalization.yaml','README.md','AUDIT.md','DEFINITIONS.md','REVIEW.md','scripts/check_package.py','scripts/check-local.ps1','verification/registered-support-provenance.json','verification/vendored-support-layout-review.json','verification/vendored-support-implementation-review.json']:
        hashes[name]=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    if write:
        (ROOT/'verification').mkdir(exist_ok=True)
        (ROOT/'verification/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
    else:
        assert json.loads((ROOT/'verification/source-hashes.json').read_text())==hashes
    print(json.dumps({'status':'pass','challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge.encode()),'hashes':hashes},indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--axiom-log');p.add_argument('--write-hashes',action='store_true');a=p.parse_args();check(a.axiom_log,a.write_hashes)
