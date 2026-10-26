from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[1];repository=root.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *a:subprocess.check_output(['git','-C',str(repository),*a])
commit='d6d42a1b3979e23289ed393ce467b1dcf260c9dc'
modules=['SourcePaths','Periods','Harmonic','LoopImage','CircleWinding','CircleData','RawLift','CirclePeriods','ACAnalysis','ACPeriods','Potential','Density','Poisson','Green','CompactGreen']
ranges={'SourcePaths': [(1, 68)], 'Periods': [(1, 61)], 'Harmonic': [(1, 19)], 'LoopImage': [(1, 18)], 'CircleWinding': [(1, 30)], 'CircleData': [(1, 39)], 'RawLift': [(1, 198)], 'CirclePeriods': [(1, 62)], 'ACAnalysis': [(1, 90)], 'ACPeriods': [(1, 36)], 'Potential': [(1, 60)], 'Density': [(1, 24)], 'Poisson': [(1, 213), (235, 235)], 'Green': [(1, 152), (156, 174), (180, 180)], 'CompactGreen': [(1, 99), (139, 139)]}
expected_refactors=[('RawLift.lean', 'rawLift_outside', '49ed98b57d6ba31b93fe3c5e89a977c7bb076dbab68fdf61ab86d1b888243ed2'), ('ACAnalysis.lean', 'primitive_lipschitz', '72e52bfe7ae133cfe585a49fcb33d2e38a57a7c50e8b516b83acf5aefd5f9292'), ('RawLift.lean', 'rawLift_projects', '137360c10e16ff8dc0ab20761f36a049238f23f8d92f1fd76f5f0ab4a427eba2'), ('RawLift.lean', 'rawLift_lipschitz', '2f240bf62612623f7208041a08a14214e33781db8d03b799b24ab7e286791ea2'), ('Green.lean', 'normalize_bound', 'd1d534da7c6412778c8af2ee34e105883a4ec866aff141edb2d54d2db7c1386b'), ('Poisson.lean', 'kernel_iff_constant', 'a8f949d9bc258e342172b15af860e9638ff050c5dee355c0d62a330cc3aac582')]
expected_omitted={'SourcePaths.lean': [], 'Periods.lean': [], 'Harmonic.lean': [], 'LoopImage.lean': [], 'CircleWinding.lean': [], 'CircleData.lean': [], 'RawLift.lean': [], 'CirclePeriods.lean': [], 'ACAnalysis.lean': [], 'ACPeriods.lean': [], 'Potential.lean': [], 'Density.lean': [], 'Poisson.lean': ['cosine', 'cosine_cover', 'cosineC2', 'cosine_zero', 'cosine_half', 'cosine_nonconstant'], 'Green.lean': ['greenMap_injective', 'exampleForcing', 'exampleForcing_nonzero'], 'CompactGreen.lean': ['green_bounded_precompact', 'green_subsequence', 'subsequence_with_raw_periods', 'green_nonzero']}
base=json.loads((root/'base-provenance.json').read_text());assert base['source_repository']=='Arthur742Ramos/Math-Formalization' and base['source_commit']==commit
assert [x['path'] for x in base['modules']]==[n+'.lean' for n in modules]
bodies={}
for row in base['modules']:
    n=row['path'][:-5];assert row['omitted_whole_declarations']==expected_omitted[row['path']];path='computational-hodge/compact-green/'+row['path'];raw=git('show',commit+':'+path);text=raw.decode();lines=text.splitlines(keepends=True);offset=[0]
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
assert imp['original_imports']==['Mathlib.Topology.Homotopy.Path', 'Mathlib.Analysis.InnerProductSpace.PiL2', 'Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional', 'Mathlib.LinearAlgebra.Isomorphisms', 'Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup', 'Mathlib.Topology.Covering.AddCircle', 'Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.Analysis.Calculus.Deriv.Basic', 'Mathlib.Analysis.Calculus.Deriv.Add', 'Mathlib.Analysis.Calculus.Deriv.Mul', 'Mathlib.Analysis.Calculus.Deriv.Comp', 'Mathlib.Topology.MetricSpace.Lipschitz', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.Analysis.Calculus.MeanValue', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.MeasureTheory.Measure.OpenPos', 'Mathlib.Analysis.Calculus.ContDiff.Deriv', 'Mathlib.Analysis.Calculus.ContDiff.Operations', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Compact', 'Mathlib.Analysis.Normed.Operator.ContinuousLinearMap', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.Basic', 'Mathlib.Topology.Sequences', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative'] and imp['retained_imports']==['Mathlib.Topology.Homotopy.Lifting', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun', 'Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff', 'Mathlib.Analysis.SpecialFunctions.Complex.Circle', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv', 'Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli', 'Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative']
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
