from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *a:subprocess.check_output(['git','-C',str(repository),*a])
commit='6dde225210537c4744b84b36a0ecd72a38710199';basepath=root/'base-provenance.json';assert sha(basepath.read_bytes())=='ea6bfb7cb164612ad63b78fe7841cabf60e18a7c09c394c5d3ef2b01d59ee4b9';base=json.loads(basepath.read_text());assert base['source_repository']=='Arthur742Ramos/Math-Formalization'and base['source_commit']==commit
assert [x['path']for x in base['modules']]==['SourcePaths.lean', 'Periods.lean', 'Harmonic.lean', 'LoopImage.lean', 'CircleWinding.lean', 'CircleData.lean', 'RawLift.lean', 'CirclePeriods.lean', 'ACAnalysis.lean', 'ACPeriods.lean', 'Potential.lean', 'Density.lean', 'Poisson.lean', 'Green.lean', 'CompactGreen.lean', 'Fredholm.lean', 'Resonance.lean']
for row in base['modules']:
 raw=git('show',commit+':'+row['source_path']);assert sha(raw)==row['source_sha256'];text=raw.decode();lines=text.splitlines(keepends=True);offsets=[0]
 for line in lines:offsets.append(offsets[-1]+len(line))
 parts=[];previous=0
 for item in row['parts']:
  a,b=item['start_character'],item['end_character'];assert previous<=a<b<=len(text);previous=b
  assert a==offsets[item['first_line']-1]and b==offsets[item['last_line']]
  assert item['sha256']==sha(text[a:b].encode())and item['start_context']==text[a:min(len(text),a+180)]and item['following_context']==text[b:min(len(text),b+180)];parts.append(text[a:b])
 assert row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+row['source_path']and row['qualify_circle']==False
 body=(row['prefix']+''.join(parts)+row['suffix']).encode();assert sha(body)==row['sha256']
 transforms_path=root/'proof-refactors.json';assert sha(transforms_path.read_bytes())=='9fdfc5c30e28a37d8ab1a943063a298c031bb66cd0ea83733c515ac74bca54f7'
 transforms=json.loads(transforms_path.read_text());assert transforms['source_commit']==commit and len(transforms['rewrites'])==42
 for change in transforms['rewrites']:
  if change['module']!=row['path']:continue
  assert sha(body)==change['before_module_sha256']
  before,after=change['old_declaration'],change['new_declaration'];assert body.decode().count(before)==1
  kind=change.get('kind','proof')
  if kind=='proof':
   name=change['theorem'];assert re.match(r'^theorem '+re.escape(name)+r'\b',before)
   old_header=before[:before.index(':=')].rstrip();new_header=after[:after.index(':=')].rstrip()
   assert old_header==new_header and sha(old_header.encode())==change['statement_sha256']
  elif kind=='adjacent-open-header':
   lines=before.splitlines();assert len(lines)>=2 and all(re.fullmatch(r'open (?!scoped\b)[^\n]+',line)for line in lines)
   names=[name for line in lines for name in line.split()[1:]]
   assert names==change['ordered_open_names']and after=='open '+' '.join(names)+'\n'
  elif kind=='comment-whitespace-reflow':
   assert before.startswith('/-!')and before.endswith('-/')and before.split()==after.split()
  else:raise AssertionError('Unknown source transformation kind')
  body=body.decode().replace(before,after,1).encode();assert sha(body)==change['after_module_sha256']
 assert body==(root/row['path']).read_bytes()

imp=json.loads((root/'import-provenance.json').read_text());pin='065356127b1dc0016f66b7283ce0ce2c4055aa55';assert imp['mathlib_commit']==pin and imp['original_imports']==['Mathlib.Topology.Homotopy.Path', 'Mathlib.Analysis.InnerProductSpace.PiL2', 'Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional', 'Mathlib.LinearAlgebra.Isomorphisms', 'Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup', 'Mathlib.Topology.Covering.AddCircle', 'Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.Analysis.Calculus.Deriv.Basic', 'Mathlib.Analysis.Calculus.Deriv.Add', 'Mathlib.Analysis.Calculus.Deriv.Mul', 'Mathlib.Analysis.Calculus.Deriv.Comp', 'Mathlib.Topology.MetricSpace.Lipschitz', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.Analysis.Calculus.MeanValue', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.MeasureTheory.Measure.OpenPos', 'Mathlib.Analysis.Calculus.ContDiff.Deriv', 'Mathlib.Analysis.Calculus.ContDiff.Operations', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Compact', 'Mathlib.Analysis.Normed.Operator.ContinuousLinearMap', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.Basic', 'Mathlib.Topology.Sequences', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative', 'Mathlib.Analysis.Normed.Operator.Mul'] and imp['retained_imports']==['Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative']
mathlib=root/'.lake/packages/mathlib';assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()==pin;nodes={}
for row in imp['source_files']:
 assert row['path']==row['module'].replace('.','/')+'.lean';raw=subprocess.check_output(['git','-C',str(mathlib),'show',pin+':'+row['path']]);assert raw==(mathlib/row['path']).read_bytes()and sha(raw)==row['sha256'];assert row['public_imports']==re.findall(r'^public import (Mathlib\.\S+)\s*$',raw.decode(),re.M);nodes[row['module']]=row
omitted=set(imp['original_imports'])-set(imp['retained_imports']);assert{x['omitted']for x in imp['witnesses']}==omitted
for item in imp['witnesses']:
 path=item['path'];assert item['retained']in imp['retained_imports']and path[0]==item['retained']and path[-1]==item['omitted']and item['omitted']in omitted
 assert len(set(path))==len(path)and all(b in nodes[a]['public_imports']for a,b in zip(path,path[1:]))
print(json.dumps(dict(status='pass',complete_predecessor_mappings=len(base['modules']),new_retained_proof_rewrites=len({(x['module'],x['theorem'])for x in transforms['rewrites']if x.get('kind','proof')=='proof'}),omitted_whole_declarations=sum(len(x['omitted_whole_declarations'])for x in base['modules']),authenticated_import_files=len(nodes),trusted_import_witnesses=len(imp['witnesses']),scope='Exact reviewed mixed public-Git fragments and exact-statement complete proof refactor chains, ordered open headers and lossless editorial whitespace. All complete final proofs remain visible. Independent semantic fidelity, builds/kernels/rendering/final evidence review remain separate.')))
