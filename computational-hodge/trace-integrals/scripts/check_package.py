#!/usr/bin/env python3
"""Exact source/provenance consistency; independent semantic and proof checks remain separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path);args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *xs:subprocess.check_output(['git','-C',str(repository),*xs])
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
base=json.loads((root/'base-provenance.json').read_text());commit='4c48f1cd68bed76d69051bdc3a706327f2d2fe27'
assert base['source_repository']=='Arthur742Ramos/Math-Formalization'and base['source_commit']==commit
names=['SourcePaths','Periods','Harmonic','LoopImage','CircleWinding','CircleData'];assert [r['path']for r in base['modules']]==[n+'.lean'for n in names]
for row in base['modules']:
 name=row['path'];paths=['computational-hodge/circle-hodge/'+name]
 if name=='CircleData.lean':paths=['computational-hodge/circle-hodge/CirclePotential.lean','computational-hodge/circle-hodge/CircleGeometry.lean']
 assert [part['source_path']for part in row['parts']]==paths
 chunks=[]
 for part in row['parts']:
  raw=git('show',commit+':'+part['source_path']);text=raw.decode();assert sha(raw)==part['source_sha256']
  assert part['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+part['source_path']
  if name=='CircleData.lean':
   bounds=(text.index('namespace ComputationalHodge.CircleHodge'),text.index('/-- A genuine real primitive'))if part['source_path'].endswith('CirclePotential.lean')else(text.index('/-- One actual circle loop'),text.index('def circleRooting'))
  else:bounds=(0,len(text))
  assert (part['start_character'],part['end_character'])==bounds
  chunk=text[bounds[0]:bounds[1]];assert sha(chunk.encode())==part['sha256']
  assert part['first_line']==text[:bounds[0]].count('\n')+1 and part['last_line']==text[:bounds[1]].count('\n');chunks.append(chunk)
 prefix='module\npublic import CircleWinding\npublic import Harmonic\npublic import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic\n@[expose] public section\n\n'if name=='CircleData.lean'else''
 separator='end ComputationalHodge.CircleHodge\n\nnamespace ComputationalHodge.LoopCharacters\nopen ComputationalPaths.Path.GeometricTopology\n'if name=='CircleData.lean'else''
 suffix='end ComputationalHodge.LoopCharacters\n'if name=='CircleData.lean'else''
 assert row['prefix']==prefix and row['separator']==separator and row['suffix']==suffix and row['replacements']==[]
 body=prefix+separator.join(chunks)+suffix
 assert body.encode()==(root/name).read_bytes()and sha(body.encode())==row['sha256']
provenance=json.loads((root/'source-provenance.json').read_text());assert len(provenance['excerpts'])==3 and provenance['upstream_commit']=='ea1367d99c7d2f3794f1299cce5b18379e9093a7'
authenticated=0
if args.upstream_root:
 upstream=lambda *xs:subprocess.check_output(['git','-C',str(args.upstream_root),*xs])
 assert upstream('rev-parse','HEAD').decode().strip()==provenance['upstream_commit']
 for row in provenance['excerpts']:
  raw=upstream('show',provenance['upstream_commit']+':'+row['path']);assert raw==(args.upstream_root/row['path']).read_bytes()and sha(raw)==row['source_sha256'];s=raw.decode();a=s.index(row['start_marker']);b=s.index(row['end_marker']);chunk=s[a:b].rstrip()+'\n'
  assert sha(chunk.encode())==row['excerpt_sha256']and chunk in(root/'SourcePaths.lean').read_text()
  assert row['first_line']==s[:a].count('\n')+1 and row['last_line']==row['first_line']+len(chunk.splitlines())-1;authenticated+=1
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];assert next(p for p in packages if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
config=json.loads((root/'comparator.json').read_text());assert (len(config['theorem_names']),len(config['definition_names']))==(42,28)
assert len(set(config['theorem_names']+config['definition_names']))==70
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']and config['challenge_module']=='Challenge'and config['solution_module']=='Solution'
def erase_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   e=s.find('\n',i);i=len(s)if e<0 else e
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
   out.append(' ')
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
for p in root.glob('*.lean'):
 s=erase_comments(p.read_text());assert s.lstrip().startswith('module'),p.name
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|set_option)\b',s),p.name
meta=json.loads((root/'formalization.yaml').read_text());prior=json.loads(git('show',commit+':computational-hodge/circle-hodge/formalization.yaml'))
for role in ['authors','responsible_maintainers']:assert meta['project'][role]==prior['project'][role]
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0 and meta['status']['axioms']==config['permitted_axioms']
assert 'analytic' in meta['status']['known_gaps'].lower()and 'circle' in meta['status']['scope'].lower()
subprocess.run(['python3',str(repository/'scripts/check_imported_definitions.py'),'--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',retained_predecessor_files=len(base['modules']),upstream_excerpts_git_authenticated=authenticated,scope='Exact source/provenance consistency. Independent semantic fidelity, native/kernel/canonical/render/browser/final evidence checks remain separate.'),indent=2))
