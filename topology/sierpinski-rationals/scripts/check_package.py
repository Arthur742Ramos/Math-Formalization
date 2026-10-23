"""Check frozen package consistency. Exact-source build/kernel/review receipts are separate."""
import argparse,hashlib,json,pathlib,re,subprocess,tomllib
ROOT=pathlib.Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--axiom-log',type=pathlib.Path)
p.add_argument('--core-source-root',type=pathlib.Path)
a=p.parse_args();sha=lambda b:hashlib.sha256(b).hexdigest()
cfg=json.loads((ROOT/'comparator.json').read_text())
assert cfg==dict(challenge_module='SRChallenge',solution_module='SRSolution',theorem_names=['SierpinskiRationals.'+n for n in ['countable_hasClopenBasis','exists_binary_scheme','BinaryScheme.code_has_both_bits','BinaryScheme.codeOrder_topology','nonempty_homeomorph','nonempty_homeomorph_iff']],definition_names=[],permitted_axioms=['propext','Quot.sound','Classical.choice'])
proof=(ROOT/'SierpinskiRationals.lean').read_bytes();assert proof==(ROOT/'SRChallenge.lean').read_bytes()
assert (ROOT/'SRSolution.lean').read_text()=='module\npublic import SierpinskiRationals\n'
assert len(proof)<=100*1024 and len(proof.splitlines())<=1000
imports=re.findall(r'^public import (\S+)',proof.decode(),re.M)
assert imports and all(i.startswith('Mathlib.') for i in imports)
files=[]
for f in ROOT.rglob('*'):
 if not f.is_file() or set(f.relative_to(ROOT).parts)&{'.lake','.git','__pycache__'}:continue
 assert not f.is_symlink(),f
 if f.suffix=='.lean':
  s=f.read_text();assert re.search(r'^module$',s,re.M) and len(s.splitlines())<=10000,f
  assert not re.search(r'\b(?:sorry|admit|axiom)\b',s),f
 assert not f.name.endswith(('.olean','.ilean','.ir','.trace','.so','.a','.o')),f
 files.append(f)
assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
lock=json.loads((ROOT/'lake-manifest.json').read_text());ml=[x for x in lock['packages'] if x['name']=='mathlib']
assert len(ml)==1 and ml[0]['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
assert all(re.fullmatch('[0-9a-f]{40}',x['rev']) and x['url'].startswith('https://github.com/') for x in lock['packages'])
lake=tomllib.loads((ROOT/'lakefile.toml').read_text());assert lake['defaultTargets']==['SierpinskiRationals','SRChallenge','SRSolution','AxiomAudit','SemanticTests','ChallengeTests']
meta=json.loads((ROOT/'formalization.yaml').read_text());roles=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert meta['project']['authors']==roles and meta['project']['responsible_maintainers']==roles
assert meta['project']['license']=='Apache-2.0'
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert set(meta['status']['axioms'])==set(cfg['permitted_axioms'])
assert 'OpenAI Codex' in json.dumps(meta)
for n in cfg['theorem_names']:assert n.split('.')[-1] in (ROOT/'README.md').read_text()
manifest=json.loads((ROOT/'verification/source-hashes.json').read_text())['files']
actual={str(f.relative_to(ROOT)) for f in files if f!=ROOT/'verification/source-hashes.json'}
assert set(manifest)==actual,('Source manifest coverage mismatch',set(manifest)^actual)
for n,d in manifest.items():assert sha((ROOT/n).read_bytes())==d,n
if a.axiom_log:
 text=a.axiom_log.read_text()
 found={n:set(re.findall(r'[A-Za-z_][\w.]*',ax)) for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)}
 assert set(cfg['theorem_names'])<=set(found) and len(found)==18
 assert all(v<=set(cfg['permitted_axioms']) for v in found.values())
if a.core_source_root:
 core=json.loads((ROOT/'verification/core-imported-definitions.json').read_text())
 for d in core['declarations']:
  b=(a.core_source_root/d['path']).read_bytes();assert sha(b)==d['file_sha256']
  text=b''.join(b.splitlines(keepends=True)[d['first_line']-1:d['last_line']]);assert text.decode()==d['text'] and sha(text)==d['excerpt_sha256']
print(json.dumps(dict(status='pass',scope='Frozen source/configuration/metadata/evidence consistency only',selected_theorems=cfg['theorem_names'],proof_sha256=sha(proof),challenge_lines=len(proof.splitlines()),challenge_bytes=len(proof),source_files=len(manifest)),indent=2))
