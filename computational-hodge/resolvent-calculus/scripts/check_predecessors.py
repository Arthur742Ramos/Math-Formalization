from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *a:subprocess.check_output(['git','-C',str(repository),*a])
commit='3aac0109c4f2bfffc9c70fc1eb3e1c2bc163a0a3';basepath=root/'base-provenance.json';assert sha(basepath.read_bytes())=='52d6a35b403f88e8f56b03ec425c61958eca076fa34aa0687ed6b535523475b9';base=json.loads(basepath.read_text());assert base['source_repository']=='Arthur742Ramos/Math-Formalization'and base['source_commit']==commit
assert [x['path']for x in base['modules']]==['SourcePaths.lean', 'Periods.lean', 'Harmonic.lean', 'LoopImage.lean', 'CircleWinding.lean', 'CircleData.lean', 'RawLift.lean', 'CirclePeriods.lean', 'ACAnalysis.lean', 'ACPeriods.lean', 'Potential.lean', 'Density.lean', 'Poisson.lean', 'Green.lean', 'CompactGreen.lean', 'Fredholm.lean', 'FullOperator.lean', 'Positive.lean']
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
 refactors=root/'proof-refactors.json';assert sha(refactors.read_bytes())=='913ba744f2c9ddc290eb0d7089cf94ded5db5d7859bb9624c6c10f00f24f0aae'
 changes=json.loads(refactors.read_text());assert changes['source_commit']==commit and len(changes['rewrites'])==2
 for change in changes['rewrites']:
  if change['module']!=row['path']:continue
  assert change['kind']=='proof' and sha(body)==change['before_module_sha256']
  before,after=change['old_declaration'],change['new_declaration'];assert body.decode().count(before)==1
  assert re.match(r'^(?:noncomputable )?(?:theorem|def) '+re.escape(change['theorem'])+r'\b',before)
  header=before[:before.index(':=')].rstrip();assert header==after[:after.index(':=')].rstrip() and sha(header.encode())==change['statement_sha256']
  body=body.decode().replace(before,after,1).encode();assert sha(body)==change['after_module_sha256']
 assert body==(root/row['path']).read_bytes()

imp=json.loads((root/'import-provenance.json').read_text());pin='065356127b1dc0016f66b7283ce0ce2c4055aa55';assert imp['mathlib_commit']==pin and imp['original_imports']==['Mathlib.Topology.Homotopy.Path', 'Mathlib.Analysis.InnerProductSpace.PiL2', 'Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional', 'Mathlib.LinearAlgebra.Isomorphisms', 'Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup', 'Mathlib.Topology.Covering.AddCircle', 'Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.Analysis.Calculus.Deriv.Basic', 'Mathlib.Analysis.Calculus.Deriv.Add', 'Mathlib.Analysis.Calculus.Deriv.Mul', 'Mathlib.Analysis.Calculus.Deriv.Comp', 'Mathlib.Topology.MetricSpace.Lipschitz', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.Analysis.Calculus.MeanValue', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.MeasureTheory.Measure.OpenPos', 'Mathlib.Analysis.Calculus.ContDiff.Deriv', 'Mathlib.Analysis.Calculus.ContDiff.Operations', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Compact', 'Mathlib.Analysis.Normed.Operator.ContinuousLinearMap', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.Basic', 'Mathlib.Topology.Sequences', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative', 'Mathlib.Analysis.Calculus.DerivativeTest', 'Mathlib.Analysis.Calculus.Deriv.Slope', 'Mathlib.Analysis.Calculus.Deriv.Inv', 'Mathlib.Analysis.Normed.Operator.BoundedLinearMaps', 'Mathlib.Analysis.Normed.Operator.NormedSpace'] and imp['retained_imports']==['Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative', 'Mathlib.Analysis.Calculus.DerivativeTest']
mathlib=root/'.lake/packages/mathlib';assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()==pin;nodes={}
for row in imp['source_files']:
 assert row['path']==row['module'].replace('.','/')+'.lean';raw=subprocess.check_output(['git','-C',str(mathlib),'show',pin+':'+row['path']]);assert raw==(mathlib/row['path']).read_bytes()and sha(raw)==row['sha256'];assert row['public_imports']==re.findall(r'^public import (Mathlib\.\S+)\s*$',raw.decode(),re.M);nodes[row['module']]=row
omitted=set(imp['original_imports'])-set(imp['retained_imports']);assert{x['omitted']for x in imp['witnesses']}==omitted
for item in imp['witnesses']:
 path=item['path'];assert item['retained']in imp['retained_imports']and path[0]==item['retained']and path[-1]==item['omitted']and item['omitted']in omitted
 assert len(set(path))==len(path)and all(b in nodes[a]['public_imports']for a,b in zip(path,path[1:]))
print(json.dumps(dict(status='pass',complete_predecessor_mappings=len(base['modules']),new_retained_proof_rewrites=2,omitted_whole_declarations=sum(len(x['omitted_whole_declarations'])for x in base['modules']),authenticated_import_files=len(nodes),trusted_import_witnesses=len(imp['witnesses']),scope='Exact reviewed mixed public-Git fragments and exact-statement complete final proof reductions. Failed intermediate authoring versions are private and excluded. Independent semantic fidelity, builds/kernels/rendering/final evidence review remain separate.')))
