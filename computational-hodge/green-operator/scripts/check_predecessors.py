from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *a:subprocess.check_output(['git','-C',str(repository),*a])
commit='d32c712e54f77f95acdedd92f3a3a0526cda3bbf'
modules=['SourcePaths','Periods','Harmonic','LoopImage','CircleWinding','CircleData','RawLift','CirclePeriods','ACAnalysis','ACPeriods','Potential','Density','Poisson']
ranges={'CirclePeriods': [(1, 8), (10, 19), (28, 71)], 'ACAnalysis': [(1, 23), (46, 48), (56, 116), (122, 122)], 'ACPeriods': [(1, 35), (63, 63)], 'Potential': [(1, 46), (53, 62), (71, 84), (105, 105)], 'Poisson': [(1, 227), (233, 246), (276, 284), (290, 323), (359, 359)]}
expected_refactors=[('RawLift.lean', 'trace_endpoints', 'd6f64180bbed2a436ad12771a35191a3fabf5db0b37d7576a11394cdbb94f0a6'), ('RawLift.lean', 'rawLift_zero', 'dd6c11a151761051949001c4c6f13f875005ef2167dc10c3864eb24d78933acf'), ('RawLift.lean', 'rawLift_continuous', '0758f52a778cdb870deeb0ee12cdab15941d45b1dc2550104ee641cfa1e06a5c'), ('RawLift.lean', 'affine_lipschitz', '8dfddcdde05d4700adddb6c5b01c2f6aba4446d874c21475ee4060f9af836987'), ('RawLift.lean', 'shift_lipschitz', 'c5ec4592205c5d705b3e5c609a86ef706fe234f7092f7e217208b281c3beae2e'), ('RawLift.lean', 'cut_lipschitz', '17acb87099ffcb003109f3dfd85ee151d4dc120aae16f9e04da44626e17baca3'), ('Potential.lean', 'realPotential_hasDerivAt', '07c54fb7adcf72ccfe680b012f1d943041854321c60af8f60fce3645ade16ac5'), ('Potential.lean', 'realPotential_contDiff', '6009deac32b220d67095838758ed3ced909be4e84882a54205464f4700824df3'), ('ACAnalysis.lean', 'lineIntegral_eq_cover', 'fc61fd89456bb2cd358981860341195763dfa90c48898bdc4078a3e9d1140c3e'), ('ACAnalysis.lean', 'line_integrand_integrable', 'c684dda906eb82c57511f686094b87f619d1adaf8835a77b81c0ab2055383906'), ('Poisson.lean', 'cosine_half', 'd03d9e045b9b5159eba56a267e87de2521e17f78235d7fab8576751a1aea4fe2'), ('Poisson.lean', 'cosine_nonconstant', 'ace15bf1ffa79e428d8597074e864ff727104a251c9e0d501724a24607258442')]
base=json.loads((root/'base-provenance.json').read_text());assert base['source_repository']=='Arthur742Ramos/Math-Formalization' and base['source_commit']==commit
assert [x['path'] for x in base['modules']]==[n+'.lean' for n in modules]
bodies={}
for row in base['modules']:
    n=row['path'][:-5];path='computational-hodge/poisson/'+row['path'];raw=git('show',commit+':'+path);text=raw.decode();lines=text.splitlines(keepends=True);offset=[0]
    for line in lines:offset.append(offset[-1]+len(line))
    bounds=[(offset[a-1],offset[b]) for a,b in ranges.get(n,[(1,len(lines))])]
    assert row['source_path']==path and row['source_url']=='https://github.com/Arthur742Ramos/Math-Formalization/blob/'+commit+'/'+path
    assert sha(raw)==row['source_sha256'] and row['prefix']==row['suffix']=='' and row['qualify_circle']==False
    assert [(x['start_character'],x['end_character']) for x in row['parts']]==bounds
    for item,(a,b) in zip(row['parts'],bounds):
        assert item['sha256']==sha(text[a:b].encode()) and item['start_context']==text[a:min(len(text),a+180)] and item['following_context']==text[b:min(len(text),b+180)]
    bodies[row['path']]=''.join(text[a:b] for a,b in bounds)
ref=json.loads((root/'proof-refactors.json').read_text());assert ref['source_commit']==commit
assert [(x['module'],x['theorem'],sha(x['new_declaration'].encode())) for x in ref['rewrites']]==expected_refactors
for item in ref['rewrites']:
    text=bodies[item['module']];old=item['old_declaration'];new=item['new_declaration']
    assert sha(text.encode())==item['before_module_sha256'] and text.count(old)==1
    assert old.startswith('theorem '+item['theorem']+' ') and new.startswith('theorem '+item['theorem']+' ')
    assert old.split(':=',1)[0]==new.split(':=',1)[0] and sha(old.split(':=',1)[0].encode())==item['statement_sha256']
    if item['insert_before']:
        text=text.replace(old,'',1);assert text.count(item['insert_before'])==1;text=text.replace(item['insert_before'],new+item['insert_before'],1)
    else:text=text.replace(old,new,1)
    assert sha(text.encode())==item['after_module_sha256'];bodies[item['module']]=text
for row in base['modules']:
    body=bodies[row['path']].encode();assert sha(body)==row['sha256'] and body==(root/row['path']).read_bytes()
imp=json.loads((root/'import-provenance.json').read_text());pin='065356127b1dc0016f66b7283ce0ce2c4055aa55';assert imp['mathlib_commit']==pin
assert imp['original_imports']==['Mathlib.Topology.Homotopy.Path', 'Mathlib.Analysis.InnerProductSpace.PiL2', 'Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional', 'Mathlib.LinearAlgebra.Isomorphisms', 'Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup', 'Mathlib.Topology.Covering.AddCircle', 'Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.Analysis.Calculus.Deriv.Basic', 'Mathlib.Analysis.Calculus.Deriv.Add', 'Mathlib.Analysis.Calculus.Deriv.Mul', 'Mathlib.Analysis.Calculus.Deriv.Comp', 'Mathlib.Topology.MetricSpace.Lipschitz', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.Analysis.Calculus.MeanValue', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.MeasureTheory.Measure.OpenPos', 'Mathlib.Analysis.Calculus.ContDiff.Deriv', 'Mathlib.Analysis.Calculus.ContDiff.Operations', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Compact', 'Mathlib.Analysis.Normed.Operator.ContinuousLinearMap'] and imp['retained_imports']==['Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv']
mathlib=root/'.lake/packages/mathlib';assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()==pin
nodes={}
for row in imp['source_files']:
    assert row['path']==row['module'].replace('.','/')+'.lean'
    raw=subprocess.check_output(['git','-C',str(mathlib),'show',pin+':'+row['path']]);assert raw==(mathlib/row['path']).read_bytes() and sha(raw)==row['sha256']
    assert row['public_imports']==re.findall(r'^public import (Mathlib\.\S+)\s*$',raw.decode(),re.M);nodes[row['module']]=row
omitted=set(imp['original_imports'])-set(imp['retained_imports']);assert {x['omitted'] for x in imp['witnesses']}==omitted
for item in imp['witnesses']:
    path=item['path'];assert item['retained'] in imp['retained_imports'] and path[0]==item['retained'] and path[-1]==item['omitted'] and item['omitted'] in omitted
    assert len(set(path))==len(path) and all(b in nodes[a]['public_imports'] for a,b in zip(path,path[1:]))
print(json.dumps(dict(status='pass',complete_predecessor_mappings=len(modules),statement_preserving_proof_refactors=len(ref['rewrites']),authenticated_import_files=len(nodes),trusted_import_witnesses=len(imp['witnesses']),scope='Exact retained source/adaptation/import consistency. Independent mathematical fidelity, compilation, kernels, rendering and final evidence review remain required.')))
