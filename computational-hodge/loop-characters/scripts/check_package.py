#!/usr/bin/env python3
"""Source/provenance consistency; proof, kernels, visual and review evidence remain separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path);args=parser.parse_args()
sha=lambda raw:hashlib.sha256(raw).hexdigest()
git=lambda *xs:subprocess.check_output(['git','-C',str(repository),*xs])
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
base=json.loads((root/'base-provenance.json').read_text());commit='5492d3284741fe4a598ae2031205f5bb024f2d6c'
assert base['source_commit']==commit and base['source_repository']=='Arthur742Ramos/Math-Formalization'
assert {r['path']for r in base['modules']}=={n+'.lean'for n in ['SourcePaths','Periods','Harmonic']}
for row in base['modules']:
 assert row['source_commit']==commit and row['source_path']=='computational-hodge/'+('finite-periods' if row['path']=='Harmonic.lean' else 'geometric-obstruction')+'/'+row['path']
 assert row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+row['source_path']
 raw=git('show',commit+':'+row['source_path']);text=raw.decode();assert sha(raw)==row['source_sha256'];chunks=[]
 for part in row['ranges']:
  chunk=text[part['start_character']:part['end_character']]
  assert sha(chunk.encode())==part['sha256']
  assert text[:part['start_character']].count('\n')+1==part['start_line']
  assert text[:part['end_character']].count('\n')==part['end_line'];chunks.append(chunk)
 retained=row['separator'].join(chunks)+row['appended_namespace_closure']
 expected_proof_adaptations=[('208bd2c717eb6d5b782d095704c8dceb208343c095ec2d85da8ef1792a9842c6', 'b029c7def24518cb82cc6c756182682bc426b162c625f9c3e0b897811d93176e'), ('bf9036617f3e3f9bc957ba96bb2c53de6df05981bdd704d4df701411e4ef2876', 'cf3d09eebb100f269c7b7d00f629b821bc9df8afd6141d51238cf9b910da5dbb')] if row['path']=='Harmonic.lean' else []
 assert [(sha(e['old'].encode()),sha(e['new'].encode()))for e in row['replacements']]==expected_proof_adaptations
 for edit in row['replacements']:
  assert retained.count(edit['old'])==1
  if edit.get('kind')=='record-law-term-proof':
   assert row['path']=='Harmonic.lean'
   assert edit['old'].startswith(("  map_add' ω η :=","  map_smul' r ω :="))
   assert edit['old'].split(':=',1)[0]==edit['new'].split(':=',1)[0]
   assert edit['new'].startswith(("  map_add' ω η := Subtype.ext <|","  map_smul' r ω := Subtype.ext <|"))
  else:
   assert edit['old'].startswith('public import ') and edit['new'].startswith('public import ')
  retained=retained.replace(edit['old'],edit['new'])
 assert retained.encode()==(root/row['path']).read_bytes() and sha(retained.encode())==row['sha256']
provenance=json.loads((root/'source-provenance.json').read_text())
assert len(provenance['excerpts'])==3 and provenance['upstream_commit']=='ea1367d99c7d2f3794f1299cce5b18379e9093a7'
authenticated=0
if args.upstream_root:
 upstream_git=lambda *xs:subprocess.check_output(['git','-C',str(args.upstream_root),*xs])
 assert upstream_git('rev-parse','HEAD').decode().strip()==provenance['upstream_commit']
 for row in provenance['excerpts']:
  raw=upstream_git('show',provenance['upstream_commit']+':'+row['path'])
  assert raw==(args.upstream_root/row['path']).read_bytes() and sha(raw)==row['source_sha256']
  text=raw.decode();start=text.index(row['start_marker']);end=text.index(row['end_marker'])
  excerpt=text[start:end].rstrip()+'\n';assert sha(excerpt.encode())==row['excerpt_sha256'] and excerpt in(root/'SourcePaths.lean').read_text()
  assert text[:start].count('\n')+1==row['first_line'] and row['last_line']==row['first_line']+len(excerpt.splitlines())-1;authenticated+=1
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
packages=json.loads((root/'lake-manifest.json').read_text())['packages']
assert next(v for v in packages if v['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
config=json.loads((root/'comparator.json').read_text());assert (len(config['theorem_names']),len(config['definition_names']))==(28,21)
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound'] and config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
def erase_comments(text):
 out=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;i+=2
  elif depth and text.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif text.startswith('--',i):
   end=text.find('\n',i);i=len(text)if end<0 else end
  elif text[i]=='"':
   i+=1
   while i<len(text):
    if text[i]=='\\':i+=2
    elif text[i]=='"':i+=1;break
    else:i+=1
   out.append(' ')
  else:out.append(text[i]);i+=1
 assert depth==0
 return ''.join(out)
for path in root.glob('*.lean'):
 text=erase_comments(path.read_text());assert text.lstrip().startswith('module'),path.name
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|set_option)\b',text),path.name
meta=json.loads((root/'formalization.yaml').read_text())
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0 and meta['status']['axioms']==config['permitted_axioms']
prior_meta=json.loads(git('show',commit+':computational-hodge/geometric-obstruction/formalization.yaml'))
for role in ['authors','responsible_maintainers']:assert meta['project'][role]==prior_meta['project'][role]
assert 'analytic' in meta['status']['known_gaps'] and 'represented' in meta['status']['scope']
subprocess.run(['python3',str(repository/'scripts/check_imported_definitions.py'),'--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',base_files_git_authenticated=len(base['modules']),upstream_excerpts_git_authenticated=authenticated,scope='Consistency and retained-source provenance only; semantic completeness and local native/canonical/kernel/render/browser/final review remain separately evidenced.'),indent=2))
