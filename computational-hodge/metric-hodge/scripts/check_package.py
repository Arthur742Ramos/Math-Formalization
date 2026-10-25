#!/usr/bin/env python3
"""Exact source/provenance consistency; independent semantic and proof checks remain separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path);args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *xs:subprocess.check_output(['git','-C',str(repository),*xs])
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
base=json.loads((root/'base-provenance.json').read_text());commit='19026134ae8481e3e40205cb3c40e766a25fc060'
assert base['source_repository']=='Arthur742Ramos/Math-Formalization'and base['source_commit']==commit
expected=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'CircleWinding', 'CircleData', 'RawLift', 'CirclePeriods', 'ACAnalysis', 'ACPeriods', 'Potential']
origins={'SourcePaths': 'automatic-lifts', 'Periods': 'automatic-lifts', 'Harmonic': 'automatic-lifts', 'LoopImage': 'automatic-lifts', 'CircleWinding': 'automatic-lifts', 'CircleData': 'ac-lifts', 'RawLift': 'automatic-lifts', 'CirclePeriods': 'automatic-lifts', 'ACAnalysis': 'ac-lifts', 'ACPeriods': 'ac-lifts', 'Potential': 'circle-hodge'}
rules={'ACPeriods': [(None, 'theorem lineIntegral_fromTrace ('), ('theorem lineIntegral_fromTrace_harmonic (', None)], 'Potential': [('/-- A genuine real primitive', 'theorem residual_exact')]}
prefixes={'Potential': 'module\npublic import ACPeriods\npublic import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff\npublic import Mathlib.Analysis.Calculus.MeanValue\n@[expose] public section\nnamespace ComputationalHodge.CircleHodge\nopen Set\n'}
suffixes={'Potential': '\nend ComputationalHodge.CircleHodge\n'}
assert [row['path']for row in base['modules']]==[n+'.lean'for n in expected]
for row in base['modules']:
 n=row['path'][:-5];source='computational-hodge/'+origins[n]+'/'+('CirclePotential'if n=='Potential'else n)+'.lean';raw=git('show',commit+':'+source)
 assert row['source_path']==source and row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+source
 text=raw.decode();bounds=[(0 if a is None else text.index(a),len(text)if b is None else text.index(b))for a,b in rules.get(n,[(None,None)])]
 assert sha(raw)==row['source_sha256']and [(x['start_character'],x['end_character'])for x in row['parts']]==bounds
 assert row['prefix']==prefixes.get(n,'')and row['suffix']==suffixes.get(n,'')
 assert all(x['sha256']==sha(text[x['start_character']:x['end_character']].encode())for x in row['parts'])
 assert row['qualify_circle']==(n in ['ACAnalysis','ACPeriods'])
 body=prefixes.get(n,'')+''.join(text[a:b]for a,b in bounds)+suffixes.get(n,'')
 if n in ['ACAnalysis','ACPeriods']:body=re.sub(r'(?<![\w.])Circle\b','CircleHodge.Circle',body)
 body=body.encode()
 assert sha(body)==row['sha256']and body==(root/row['path']).read_bytes()
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
config=json.loads((root/'comparator.json').read_text());assert (len(config['theorem_names']),len(config['definition_names']))==(46, 42)
assert len(set(config['theorem_names']+config['definition_names']))==88
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
meta=json.loads((root/'formalization.yaml').read_text());prior=json.loads(git('show',commit+':computational-hodge/automatic-lifts/formalization.yaml'))
for role in ['authors','responsible_maintainers']:assert meta['project'][role]==prior['project'][role]
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0 and meta['status']['axioms']==config['permitted_axioms']
assert 'analytic' in meta['status']['known_gaps'].lower()and 'circle' in meta['status']['scope'].lower()
subprocess.run(['python3',str(repository/'scripts/check_imported_definitions.py'),'--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',retained_predecessor_files=len(base['modules']),upstream_excerpts_git_authenticated=authenticated,scope='Exact source/provenance consistency. Independent semantic fidelity, native/kernel/canonical/render/browser/final evidence checks remain separate.'),indent=2))
