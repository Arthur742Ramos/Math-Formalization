"""Check roles, pinned dependencies, canonical statements and preserved support."""
import argparse,hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[1]
TEAM=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
AXIOMS={'propext','Classical.choice','Quot.sound'}
THEOREMS=['PerfectImage.exists_radius_star_subset','PerfectImage.sigmaLocallyFiniteBasis_image','PerfectImage.metrizable_image','PerfectImage.metrizable_image_of_proper','PerfectImage.exists_compatibleMetric']
DEFINITIONS=['PerfectImage.upperImage','PerfectImage.fiberNeighborhood']

def check(log,write):
    assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
    lock=json.loads((ROOT/'lake-manifest.json').read_text())
    assert lock['name']=='perfectMetrizableImages'
    assert next(p for p in lock['packages'] if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
    config=json.loads((ROOT/'comparator.json').read_text())
    assert config['theorem_names']==THEOREMS and config['definition_names']==DEFINITIONS
    assert set(config['permitted_axioms'])==AXIOMS
    assert config['challenge_module']=='PerfectImageChallenge' and config['solution_module']=='PerfectImageSolution'
    challenge=(ROOT/'PerfectImageChallenge.lean').read_text(encoding='utf-8')
    assert len(challenge.splitlines())<=1000 and len(challenge.encode())<=100*1024
    assert all(i.startswith('Mathlib.') for i in re.findall(r'^public import (\S+)$',challenge,re.M))
    assert 'SecondCountableTopology' not in challenge and 'SeparableSpace' not in challenge
    assert '@[expose] public section' in challenge
    metadata=json.loads((ROOT/'formalization.yaml').read_text(encoding='utf-8'))
    assert metadata['project']['name']=='Perfect images of metrizable spaces'
    for field in ['authors','responsible_maintainers']:
        assert metadata['project'][field]==TEAM
    readme=(ROOT/'README.md').read_text(encoding='utf-8')
    assert all(name in readme for name in TEAM) and 'no human review is claimed' in readme
    hashes={}
    for path in ROOT.rglob('*.lean'):
        if '.lake' in path.relative_to(ROOT).parts:continue
        text=path.read_text(encoding='utf-8')
        assert re.search(r'^module\s*$',text,re.M),str(path)
        assert not re.search(r'\b(sorry|admit|axiom)\b',text),str(path)
        assert len(text.splitlines())<=10000
        hashes[path.relative_to(ROOT).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    support=json.loads((ROOT/'verification/registered-support-provenance.json').read_text())
    assert len(support)==5
    for name,record in support.items():
        assert hashes[name]==record['adapted_sha256']
        text=(ROOT/name).read_text(encoding='utf-8')
        if name.startswith('NagataSmirnovSupport/'):
            assert record['source_commit']=='6aa68b2cb67719a187e64de29567443575eb560e'
            text=re.sub(r'/\- Reused from registered PALOMAR-2026-10-14-000001,.*?\-/\n\n','',text,flags=re.S)
            text=text.replace('public import NagataSmirnovSupport.','public import ')
        else:
            assert record['source_commit']=='984a610395e195b8d3ca0cd88282ef343e74d33d'
            text=re.sub(r'/\- Credited reuse of registered PALOMAR-2026-10-13-000004 v1,.*?\-/\n','',text,flags=re.S)
        assert hashlib.sha256(text.encode()).hexdigest()==record['original_sha256'],(name,'registered source changed')
    # Every included proof is the exact modular source body, with public exposure
    # added only where necessary for canonical statement comparison.
    for name in list(support)+['FiberNeighborhoods.lean','PerfectImage.lean']:
        text=(ROOT/name).read_text(encoding='utf-8')
        start=text.index('@[expose] public section') if '@[expose] public section' in text else text.index('public section')
        body=text[start:]
        if not body.startswith('@[expose]'):body='@[expose] '+body
        assert body in challenge,(name,'Challenge does not contain exact proof body')
    workflows=ROOT.parents[1]/'.github/workflows'
    for suffix in ['.yml','-renderer.yml']:
        name='palomar-perfect-image'+suffix;text=(workflows/name).read_text()
        assert '.github/workflows/'+name in text
        assert "branches: ['topology/perfect-metrizable-images']" in text
        assert 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44' in text
        hashes['../../.github/workflows/'+name]=hashlib.sha256((workflows/name).read_bytes()).hexdigest()
    text=(workflows/'palomar-perfect-image.yml').read_text()
    request=re.search(r'^\s+request_id: (\S+)\s*$',text,re.M)
    assert request and re.fullmatch(r'[0-9a-z]{12}',request.group(1))
    if log:
        body=pathlib.Path(log).read_text(encoding='utf-8-sig')
        reports=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",body))
        reports.update({n:'' for n in re.findall(r"'([^']+)' does not depend on any axioms",body)})
        assert len(reports)==15,len(reports)
        assert all(n in reports for n in THEOREMS+DEFINITIONS)
        assert all({a.strip() for a in v.split(',') if a.strip()}<=AXIOMS for v in reports.values())
    for name in ['.gitattributes','lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json','formalization.yaml','README.md','AUDIT.md','DEFINITIONS.md','REVIEW.md','scripts/check_package.py','scripts/check-local.ps1','verification/registered-support-provenance.json','verification/internal-review-summary.json','verification/local-axioms.txt']:
        hashes[name]=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    if write:(ROOT/'verification/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:assert json.loads((ROOT/'verification/source-hashes.json').read_text())==hashes
    print(json.dumps({'status':'pass','selected_theorems':len(THEOREMS),'selected_definitions':len(DEFINITIONS),'preserved_support_modules':len(support),'challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge.encode()),'hashes':hashes},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--axiom-log');p.add_argument('--write-hashes',action='store_true');a=p.parse_args();check(a.axiom_log,a.write_hashes)
