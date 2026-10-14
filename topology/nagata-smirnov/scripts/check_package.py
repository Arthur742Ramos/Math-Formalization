"""Audit exact pins, source limits, definitions, author roles and axiom closures."""
import argparse,hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[1]
TEAM=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
AXIOMS={'propext','Classical.choice','Quot.sound'}
def check(log,write):
    assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
    lock=json.loads((ROOT/'lake-manifest.json').read_text());assert lock['name']=='nagataSmirnov'
    assert next(p for p in lock['packages'] if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
    config=json.loads((ROOT/'comparator.json').read_text());assert set(config['permitted_axioms'])==AXIOMS
    assert len(config['theorem_names'])==6
    challenge=(ROOT/'Challenge.lean').read_text(encoding='utf-8')
    assert len(challenge.splitlines())<=1000 and len(challenge.encode())<=100*1024
    assert all(x.startswith('Mathlib.') for x in re.findall(r'^public import (\S+)$',challenge,re.M))
    metadata=json.loads((ROOT/'formalization.yaml').read_text(encoding='utf-8'))
    for field in ['authors','responsible_maintainers']:assert metadata['project'][field]==TEAM
    assert re.search(r'∃ B : ℕ → Set \(Set X\)',challenge)
    assert '@[expose] public section' in challenge
    assert 'SecondCountableTopology' not in challenge and 'SeparableSpace' not in challenge
    hashes={}
    for path in ROOT.glob('*.lean'):
        text=path.read_text(encoding='utf-8')
        assert re.search(r'^module\s*$',text,re.M),str(path)
        assert not re.search(r'\b(sorry|admit|axiom)\b',text),str(path)
        assert len(text.splitlines())<=10000
        hashes[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
    if log:
        reports=dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",pathlib.Path(log).read_text(encoding='utf-8-sig')))
        for name in config['theorem_names']:
            assert name in reports,name
            assert {s.strip() for s in reports[name].split(',') if s.strip()}<=AXIOMS,name
        assert len(reports)==15,len(reports)
        assert all({s.strip() for s in a.split(',') if s.strip()}<=AXIOMS for a in reports.values())
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json','formalization.yaml','README.md','AUDIT.md','DEFINITIONS.md','REVIEW.md']:
        hashes[name]=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    if write:
        (ROOT/'verification').mkdir(exist_ok=True)
        (ROOT/'verification/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
    print(json.dumps({'status':'pass','challenge_lines':len(challenge.splitlines()),'challenge_bytes':len(challenge.encode()),'hashes':hashes},indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--axiom-log');p.add_argument('--write-hashes',action='store_true');a=p.parse_args();check(a.axiom_log,a.write_hashes)
