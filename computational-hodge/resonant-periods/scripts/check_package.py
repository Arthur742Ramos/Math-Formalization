from pathlib import Path
import argparse,hashlib,json,os,re,subprocess

if not __debug__:
 raise RuntimeError('This checker must run without Python optimization')

ROOT=Path(__file__).resolve().parents[1]
os.environ['GIT_OPTIONAL_LOCKS']='0'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(root,*args):return subprocess.check_output(['git','-C',str(root),*args])

def main():
 ap=argparse.ArgumentParser(description='Check exact pinned path provenance and candidate package consistency; not a proof or release verification.')
 ap.add_argument('--upstream-root',type=Path,required=True);ap.add_argument('--predecessor-root',type=Path,required=True);args=ap.parse_args()
 prov=json.loads((ROOT/'source-provenance.json').read_text());port=(ROOT/'SourcePaths.lean').read_text();commit='ea1367d99c7d2f3794f1299cce5b18379e9093a7'
 assert prov['upstream_commit']==commit and len(prov['excerpts'])==3
 assert sha((ROOT/'source-provenance.json').read_bytes())=='4951794d109a9f78e8b169a21ec653de412a10f9c1ff7f7ea49b2f96866e4879'
 expected={('ComputationalPaths/Path/Topology/OpenGeometricComputationalPath.lean','structure GeometricStepSystem','/-- Computational depth',True),('ComputationalPaths/Path/Topology/ContinuousGeometricStepSystem.lean','structure ContinuousGeometricStepSystem','namespace ContinuousGeometricStepSystem',False),('ComputationalPaths/Path/Topology/ScopedGeometricRewrite.lean','structure ScopedGeometricRewritePresentation','/-! ## Scoped closure -/',False)}
 assert {(e['path'],e['start_marker'],e['end_marker'],e['namespace_closure_added']) for e in prov['excerpts']}==expected
 assert all(e['repository']=='Arthur742Ramos/TopologicalComputationalPaths' for e in prov['excerpts'])
 assert git(args.upstream_root,'rev-parse','HEAD').decode().strip()==commit
 for e in prov['excerpts']:
  assert e['commit']==commit and not git(args.upstream_root,'status','--porcelain','--',e['path']).strip()
  raw=git(args.upstream_root,'show',commit+':'+e['path']);assert raw==(args.upstream_root/e['path']).read_bytes() and sha(raw)==e['source_sha256']
  text=raw.decode();start=text.index(e['start_marker']);end=text.index(e['end_marker']);assert start<end;chunk=text[start:end].rstrip()+'\n'
  assert sha(chunk.encode())==e['excerpt_sha256'] and chunk in port
  assert e['first_line']==text[:start].count('\n')+1 and e['last_line']==e['first_line']+len(chunk.splitlines())-1
  adjusted=chunk+('\nend GeometricTrace\n' if e['namespace_closure_added'] else '')
  assert sha(adjusted.encode())==e['port_chunk_sha256'] and adjusted in port
 surface0=port[port.index('structure GeometricStepSystem'):port.index('end ComputationalPaths.Path.GeometricTopology')]
 lines=surface0.splitlines();formatted=[];i=0
 while i<len(lines):
  line=lines[i];i+=1
  if not line.strip():continue
  if line.startswith(('structure ContinuousGeometricStepSystem','structure ScopedGeometricRewritePresentation')):
   chunks=[line.strip()]
   while not chunks[-1].endswith('where'):
    assert i<len(lines);chunks.append(lines[i].strip());i+=1
   line=' '.join(chunks)
  formatted.append(line)
 expected_surface='\n'.join(formatted)+'\n'
 for filename in ['Challenge.lean','Solution.lean']:
  text=(ROOT/filename).read_text();surface=text[text.index('structure GeometricStepSystem'):text.index('end ComputationalPaths.Path.GeometricTopology')]
  assert surface==expected_surface
 base=json.loads((ROOT/'base-provenance.json').read_text());commit='f9c1eec39bd7f6d4873e1281e2e1de62d80b3750';assert base['source_commit']==commit
 assert sha((ROOT/'base-provenance.json').read_bytes())=='29fcf7617b9588fcb6828582c07069c1f9b1c32f9ccd6cec3b561b601f1a9b23'
 assert base['repository']=='Arthur742Ramos/Math-Formalization'
 assert len(base['modules'])==3 and {m['path'] for m in base['modules']}=={'SourcePaths.lean','Challenge.lean','Solution.lean'}
 for m in base['modules']:
  expected_path='computational-hodge/arclength-modes/'+('SourcePaths.lean' if m['path']=='SourcePaths.lean' else 'Challenge.lean')
  assert m['source_path']==expected_path and m['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+expected_path
  raw=git(args.predecessor_root,'show',commit+':'+m['source_path']);out=(ROOT/m['path']).read_bytes();assert sha(raw)==m['source_sha256'] and sha(out)==m['candidate_sha256']
  old=raw.decode().splitlines(keepends=True);new=out.decode().splitlines(keepends=True);i=k=0
  for op in m['operations']:
   assert op['source_first_line']==i+1 and op['output_first_line']==k+1
   j=op['source_last_line'];l=op['output_last_line'];assert i<=j<=len(old) and k<=l<=len(new)
   before=''.join(old[i:j]).encode();after=''.join(new[k:l]).encode()
   if op['operation']=='equal':assert before==after and sha(before)==op['sha256']
   else:assert op['operation'] in {'insert','replace','delete'} and sha(before)==op['removed_source_sha256'] and sha(after)==op['added_sha256'] and after==op['added_text'].encode()
   i=j;k=l
  assert i==len(old) and k==len(new)
 config=json.loads((ROOT/'comparator.json').read_text());selected=config['theorem_names']+config['definition_names']
 assert sha((ROOT/'comparator.json').read_bytes())=='03ffdfcc031932501ef1ade4a7b86a7927fb8f63a326d87427a828d369476628'
 assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
 assert len(config['theorem_names'])==12 and len(config['definition_names'])==25 and len(set(selected))==37
 assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
 assert (ROOT/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
 assert (ROOT/'lake-manifest.json').read_bytes()==git(args.predecessor_root,'show',commit+':computational-hodge/arclength-modes/lake-manifest.json')
 lock=json.loads((ROOT/'lake-manifest.json').read_text());assert next(p for p in lock['packages'] if p['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
 meta=json.loads((ROOT/'formalization.yaml').read_text());prior=json.loads(git(args.predecessor_root,'show',commit+':computational-hodge/arclength-modes/formalization.yaml'))
 for role in ['authors','responsible_maintainers']:assert meta['project'][role]==prior['project'][role]
 assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0 and meta['status']['axioms']==config['permitted_axioms']
 assert (ROOT/'Challenge.lean').read_bytes()==(ROOT/'Solution.lean').read_bytes()
 print(json.dumps({'status':'pass','upstream_commit':prov['upstream_commit'],'upstream_excerpts_authenticated':3,'predecessor_commit':base['source_commit'],'mapped_modules':len(base['modules']),'selected_count':len(selected),'scope':'Pinned source, exact deterministic rendered path formatting, line-level mapping, roles and predecessor lockfile equality only. This does not prove semantic fidelity or perform kernel, canonical or rendering checks.'},indent=2))
if __name__=='__main__':main()
