"""Validate source consistency only; native/canonical/review receipts are separate."""
import pathlib,json,re,hashlib,tomllib,argparse
P=pathlib.Path(__file__).resolve().parents[1];a=argparse.ArgumentParser();a.add_argument('--axiom-log',type=pathlib.Path);args=a.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cfg=json.loads((P/'comparator.json').read_text())
assert cfg['challenge_module']=='LEChallenge' and cfg['solution_module']=='LESolution'
assert cfg['definition_names']==[] and len(cfg['theorem_names'])==8
assert cfg['permitted_axioms']==['propext','Quot.sound','Classical.choice']
assert (P/'Lavrentieff.lean').read_bytes()==(P/'LEChallenge.lean').read_bytes()
assert (P/'LESolution.lean').read_text()=='module\npublic import Lavrentieff\n'
files={str(p.relative_to(P)):p for p in P.rglob('*') if p.is_file() and not set(p.relative_to(P).parts)&{'.lake','.git','__pycache__'}}
for name,p in files.items():
 assert not p.is_symlink(),name
 if p.suffix=='.lean':
  s=p.read_text();assert re.search(r'^module$',s,re.M) and len(s.splitlines())<=10000
  assert not re.search(r'\b(?:sorry|admit|axiom)\b',s),name
 assert not p.name.endswith(('.olean','.ilean','.ir','.trace','.so','.a','.o')),name
proof=(P/'LEChallenge.lean').read_text();assert len(proof.encode())<=100*1024 and len(proof.splitlines())<=1000
assert all(i.startswith('Mathlib.') for i in re.findall(r'^public import (\S+)',proof,re.M))
assert (P/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
lock=json.loads((P/'lake-manifest.json').read_text());assert lock['name']=='lavrentieffExtension'
assert next(p for p in lock['packages'] if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
assert all(re.fullmatch('[0-9a-f]{40}',p['rev']) for p in lock['packages'])
assert tomllib.loads((P/'lakefile.toml').read_text())['defaultTargets']==['Lavrentieff','LEChallenge','LESolution','AxiomAudit','SemanticTests','ChallengeTests']
m=json.loads((P/'formalization.yaml').read_text());roles=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert m['project']['authors']==roles and m['project']['responsible_maintainers']==roles
assert m['project']['license']=='Apache-2.0' and m['status']['sorry_count']==m['status']['sorry_in_definitions']==0
assert set(m['status']['axioms'])==set(cfg['permitted_axioms']) and 'OpenAI Codex' in json.dumps(m)
for n in cfg['theorem_names']:assert n.split('.')[-1] in (P/'README.md').read_text()
manifest=json.loads((P/'verification/source-hashes.json').read_text())['files']
assert set(manifest)==set(files)-{'verification/source-hashes.json'}
assert all(sha(files[n])==h for n,h in manifest.items())
if args.axiom_log:
 text=args.axiom_log.read_text();found={n:set(re.findall(r'[A-Za-z_][\w.]*',v)) for n,v in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 assert set(found)==set(cfg['theorem_names']),found
 assert all(v<=set(cfg['permitted_axioms']) for v in found.values())
print(json.dumps(dict(status='pass',scope=__doc__,proof_sha256=sha(P/'Lavrentieff.lean'),theorems=cfg['theorem_names'],files=len(files),lines=len(proof.splitlines())),indent=2))
