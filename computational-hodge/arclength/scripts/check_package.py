#!/usr/bin/env python3
"""Exact source/provenance consistency; independent semantic and proof checks remain separate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--upstream-root',type=Path);args=parser.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *xs:subprocess.check_output(['git','-C',str(repository),*xs])
subprocess.run(['python3',str(root/'scripts/make_surface.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
base=json.loads((root/'base-provenance.json').read_text());commit='69fc594b9bac4757f44b9647618f581931e2af2a'
assert base['source_repository']=='Arthur742Ramos/Math-Formalization'and base['source_commit']==commit
expected=['SourcePaths', 'Periods', 'Harmonic', 'LoopImage', 'CircleWinding', 'CircleData', 'RawLift', 'CirclePeriods', 'LiftFoundation', 'TraceFoundation', 'Energy', 'Density', 'Primitive']
origins={'SourcePaths': 'metric-hodge', 'Periods': 'metric-hodge', 'Harmonic': 'metric-hodge', 'LoopImage': 'metric-hodge', 'CircleWinding': 'metric-hodge', 'CircleData': 'metric-hodge', 'RawLift': 'metric-hodge', 'CirclePeriods': 'metric-hodge', 'LiftFoundation': 'automatic-lifts', 'TraceFoundation': 'automatic-lifts', 'Energy': 'automatic-lifts', 'Density': 'metric-hodge', 'Primitive': 'metric-hodge'}
source_names={'Density': 'Metric', 'Primitive': 'ACAnalysis'}
rules={'Density': [('/-- Positive continuous length density', '/-- Coordinate star from one-form'), ('/-- Positive nonconstant continuous density', 'theorem example_nonconstant')], 'Primitive': [('noncomputable def primitive', 'theorem cover_integrand_integrable')]}
prefixes={'Density': 'module\npublic import Energy\npublic import Mathlib.Analysis.SpecialFunctions.Complex.Circle\npublic import Mathlib.MeasureTheory.Measure.OpenPos\n@[expose] public section\nnamespace ComputationalHodge.MetricHodge\nopen ComputationalHodge.CircleHodge MeasureTheory Set\n', 'Primitive': 'module\npublic import Density\n@[expose] public section\nnamespace ComputationalHodge.ACLifts\nopen ComputationalHodge.CircleHodge\nopen MeasureTheory Set\nopen scoped NNReal\n'}
suffixes={'Density': '\nend ComputationalHodge.MetricHodge\n', 'Primitive': '\nend ComputationalHodge.ACLifts\n'}
assert [row['path']for row in base['modules']]==[n+'.lean'for n in expected]
for row in base['modules']:
 n=row['path'][:-5];source='computational-hodge/'+origins[n]+'/'+source_names.get(n,n)+'.lean';raw=git('show',commit+':'+source)
 assert row['source_path']==source and row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+source
 text=raw.decode();bounds=[(0 if a is None else text.index(a),len(text)if b is None else text.index(b))for a,b in rules.get(n,[(None,None)])]
 assert sha(raw)==row['source_sha256']and [(x['start_character'],x['end_character'])for x in row['parts']]==bounds
 assert row['prefix']==prefixes.get(n,'')and row['suffix']==suffixes.get(n,'')and row['qualify_circle']==False
 assert all(x['sha256']==sha(text[x['start_character']:x['end_character']].encode())for x in row['parts'])
 body=(prefixes.get(n,'')+''.join(text[a:b]for a,b in bounds)+suffixes.get(n,'')).encode()
 assert sha(body)==row['sha256']and body==(root/row['path']).read_bytes()
core=json.loads((root/'verification/lean-core-definitions.json').read_text());assert core['name']=='Function.Surjective'and core['compiler_commit']=='11acb17ec6b07a8f9e9173e6845197929540936b'
assert core['source_sha256']=='88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030'and core['excerpt_sha256']=='81f3c1294b8b4f215a4b094823922dbd95234cd6a53280e94f6fd6d7280c0148'
assert core['path']=='Init/Data/Function.lean'and core['first_line']==59 and core['last_line']==63
core_path=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root,text=True).strip())/'src/lean'/core['path'];raw=core_path.read_bytes();excerpt=b''.join(raw.splitlines(keepends=True)[58:63]);assert sha(raw)==core['source_sha256']and sha(excerpt)==core['excerpt_sha256']and excerpt.decode()==core['excerpt']
assert core['url']=='https://github.com/leanprover/lean4/blob/'+core['compiler_commit']+'/src/Init/Data/Function.lean#L59-L63'
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
config=json.loads((root/'comparator.json').read_text());assert (len(config['theorem_names']),len(config['definition_names']))==(41, 40)
assert len(set(config['theorem_names']+config['definition_names']))==81
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
meta=json.loads((root/'formalization.yaml').read_text());prior=json.loads(git('show',commit+':computational-hodge/metric-hodge/formalization.yaml'))
for role in ['authors','responsible_maintainers']:assert meta['project'][role]==prior['project'][role]
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0 and meta['status']['axioms']==config['permitted_axioms']
assert 'analytic' in meta['status']['known_gaps'].lower()and 'circle' in meta['status']['scope'].lower()
subprocess.run(['python3',str(repository/'scripts/check_imported_definitions.py'),'--project-path',str(root),'--dependency-root',str(root/'.lake/packages/mathlib')],check=True)
print(json.dumps(dict(status='pass',retained_predecessor_files=len(base['modules']),upstream_excerpts_git_authenticated=authenticated,scope='Exact source/provenance consistency. Independent semantic fidelity, native/kernel/canonical/render/browser/final evidence checks remain separate.'),indent=2))
