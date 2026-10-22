"""Check frozen source consistency; build/kernel/review receipts have separate scopes."""
import argparse,hashlib,json,pathlib,re,tomllib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--axiom-log',type=pathlib.Path)
parser.add_argument('--core-source-root',type=pathlib.Path)
args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
cfg=json.loads((ROOT/'comparator.json').read_text())
names=['BaireCharacterization.exists_clopen_partition', 'BaireCharacterization.exists_clopen_scheme', 'BaireCharacterization.ClopenScheme.image_cylinder', 'BaireCharacterization.nonempty_homeomorph_of_completeSpace', 'BaireCharacterization.nonempty_homeomorph', 'BaireCharacterization.baire_hasClopenBasis', 'BaireCharacterization.baire_compactInteriorEmpty', 'BaireCharacterization.nonempty_homeomorph_iff']
assert cfg['theorem_names']==names and cfg['definition_names']==[]
assert cfg['challenge_module']=='BCChallenge' and cfg['solution_module']=='BCSolution'
assert cfg['permitted_axioms']==['propext','Quot.sound','Classical.choice']
proof=(ROOT/'BaireCharacterization.lean').read_bytes()
assert proof==(ROOT/'BCChallenge.lean').read_bytes()
assert (ROOT/'BCSolution.lean').read_text()=='module\npublic import BaireCharacterization\n'
compiled_suffixes=('.olean','.ilean','.ir','.ir.sig','.olean.private','.olean.server')
files=[]
for f in ROOT.rglob('*'):
 if not f.is_file() or set(f.relative_to(ROOT).parts)&{'.lake','.git','__pycache__'}:continue
 if f.name.endswith(compiled_suffixes):
  assert subprocess.run(['git','check-ignore','--no-index','--quiet',str(f)],cwd=ROOT).returncode==0,f
  continue
 files.append(f)
for f in [f for f in files if f.suffix=='.lean']:
 assert not f.is_symlink()
 text=f.read_text()
 assert re.search(r'^module$',text,re.M),f
 assert not re.search(r'\b(?:sorry|admit|axiom)\b',text),f
 assert len(text.splitlines())<=10000,f
assert len(proof)<=100*1024 and len(proof.splitlines())<=1000
imports=re.findall(r'^public import (\S+)',proof.decode(),re.M)
assert imports==['Mathlib.Topology.MetricSpace.Polish','Mathlib.Topology.MetricSpace.CantorScheme','Mathlib.Order.Disjointed','Mathlib.Basic.Denumerable']
assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
lock=json.loads((ROOT/'lake-manifest.json').read_text())
mathlib=[p for p in lock['packages'] if p['name']=='mathlib']
assert len(mathlib)==1 and mathlib[0]['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
lake=tomllib.loads((ROOT/'lakefile.toml').read_text())
assert lake['defaultTargets']==['BaireCharacterization','BCChallenge','BCSolution','AxiomAudit','SemanticTests','ChallengeTests']
meta=json.loads((ROOT/'formalization.yaml').read_text())
roles=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert meta['project']['authors']==roles and meta['project']['responsible_maintainers']==roles
assert meta['project']['license']=='Apache-2.0'
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert set(meta['status']['axioms'])==set(cfg['permitted_axioms'])
assert 'OpenAI Codex' in json.dumps(meta)
for n in names:
 assert n.split('.')[-1] in (ROOT/'README.md').read_text()
manifest=json.loads((ROOT/'verification/source-hashes.json').read_text())
actual={str(f.relative_to(ROOT)) for f in files if f!=ROOT/'verification/source-hashes.json'}
assert set(manifest)==actual,('Source manifest coverage mismatch',set(manifest)^actual)
for name,digest in manifest.items():
 assert not name.endswith(compiled_suffixes),name
 f=ROOT/name
 assert f.resolve().is_relative_to(ROOT.resolve()) and not f.is_symlink()
 assert sha(f.read_bytes())==digest,name
if args.axiom_log:
 text=args.axiom_log.read_text()
 found={n:set(re.findall(r'[A-Za-z_][\w.]*',a)) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 assert set(names)<=set(found)
 for n,axioms in found.items():assert axioms<=set(cfg['permitted_axioms']),(n,axioms)
if args.core_source_root:
 core=json.loads((ROOT/'verification/core-imported-definitions.json').read_text())
 assert core['compiler_commit']=='11acb17ec6b07a8f9e9173e6845197929540936b'
 for d in core['declarations']:
  b=(args.core_source_root/d['path']).read_bytes()
  assert sha(b)==d['file_sha256']
  excerpt=b''.join(b.splitlines(keepends=True)[d['first_line']-1:d['last_line']])
  assert excerpt.decode()==d['text'] and sha(excerpt)==d['excerpt_sha256']
print(json.dumps(dict(status='pass',scope='Source/configuration/metadata/retained evidence consistency only',
 selected_theorems=names,definition_holes=0,challenge_sha256=sha(proof),source_files=len(manifest)),indent=2))
