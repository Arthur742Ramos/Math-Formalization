"""Metric-graph static guards; these do not prove Lean elaboration."""
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
package = ROOT / 'computational-hodge/metric-graph-resonance'
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
import check_imported_definitions as checker
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest_key = 'verification/material-imported-definitions.json'
initial = json.loads((package / manifest_key).read_text(encoding='utf8'))
names = {manifest_key, 'lake-manifest.json', 'lean-toolchain', 'comparator.json',
         'lakefile.toml', initial['documentation']}
names.update(m['path'] for m in initial['checked_bridge_modules'])
names.update(m['path'] for m in initial['checked_bridge_importers'])
files = {}
for name in names:
    rel = PurePosixPath(name)
    if rel.is_absolute() or not rel.parts or any(p in {'.', '..'} for p in rel.parts):
        raise ValueError('unsafe fixture path')
    p = package
    for part in rel.parts:
        p = p / part
        if p.is_symlink(): raise ValueError('fixture symlink')
    files[name] = p.read_bytes().decode('utf8')

class MemoryFile:
    def __init__(self,value): self.value=value
    def read_text(self): return self.value
    def read_bytes(self): return self.value.encode()

def run_check(overrides=None):
    current = dict(files)
    current.update(overrides or {})
    def local_file(_root,name):
        if name not in current: raise ValueError('missing synthetic file')
        return MemoryFile(current[name])
    with patch.object(checker,'local_file',side_effect=local_file):
        return checker.check(package)

def encoded(data): return json.dumps(data,ensure_ascii=False)

class StructuralControls(unittest.TestCase):
    def test_current_proposal_passes_static_only(self):
        result = run_check()
        self.assertEqual(result['upstream_origin'],'not-checked')
        self.assertIn('separate actual Lean build required',result['bridge_compilation'])

    def test_support_removal_and_retarget_fail(self):
        for name in ('ContinuousWithinAt','TopologicalSpace','Real.sin','Real.cos','HasDerivAt'):
            for change in ('remove','retarget'):
                data=copy.deepcopy(initial)
                row=next(r for r in data['material_declarations'] if r['name']==name)
                if change=='remove': row.pop('supporting_excerpts_draft')
                else: row['supporting_excerpts_draft'][0]='metric_Filter_Tendsto' if name != 'ContinuousWithinAt' else 'metric_complex_sine_cosine'
                with self.subTest(name=name,change=change), self.assertRaises(ValueError):
                    run_check({manifest_key:encoded(data)})

    def test_valid_support_names_cannot_be_swapped(self):
        data=copy.deepcopy(initial)
        excerpts={e['name']:e for s in data['source_files'] for e in s['excerpts']}
        a,b=excerpts['metric_Filter_Tendsto'],excerpts['metric_quotient_topology_instance']
        a['name'],b['name']=b['name'],a['name']
        with self.assertRaisesRegex(ValueError,'Retargeted pinned metric support'):
            run_check({manifest_key:encoded(data)})

    def test_role_and_graph_support_mutations_fail(self):
        data=copy.deepcopy(initial)
        row=next(r for r in data['material_declarations'] if r['name']=='MeasureTheory.ae')
        row['use_roles_draft']['semantic_expansion'].remove('MetricGraphTraceDensity.concat_density_integrable')
        with self.assertRaisesRegex(ValueError,'Missing reviewed metric semantic role'):
            run_check({manifest_key:encoded(data)})
        data=copy.deepcopy(initial)
        row=next(r for r in data['material_declarations'] if r['name']=='TopologicalSpace')
        row['supporting_uses_draft']['metric_quotient_topology_instance'].append(
            'ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize')
        with self.assertRaisesRegex(ValueError,'Missing or changed metric supporting uses'):
            run_check({manifest_key:encoded(data)})

    def test_each_support_use_map_is_required(self):
        for name in ('ContinuousWithinAt','TopologicalSpace','Real.sin','Real.cos',
                     'HasFDerivAtFilter','MeasureTheory.Integrable','Real.volume_eq_stieltjes_id','HasDerivAt'):
            data=copy.deepcopy(initial)
            row=next(r for r in data['material_declarations'] if r['name']==name)
            row.pop('supporting_uses_draft')
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'Missing or changed metric supporting uses'):
                run_check({manifest_key:encoded(data)})

    def test_each_reviewed_role_category_is_required(self):
        cases=(('MeasureTheory.Integrable','semantic_expansion','MetricGraphPathPrototype.graphPotential'),
               ('MeasureTheory.ae','semantic_expansion','MetricGraphTraceDensity.concat_density_integrable'),
               ('Filter.Eventually','semantic_expansion','MetricGraphResonancePrototype.sine_wronskian'),
               ('TopologicalSpace','statement_or_definition','MetricGraphPathPrototype.traceChartIntegral'),
               ('Continuous','semantic_expansion','MetricGraphPathPrototype.edgeStepSystem'))
        for name,role,use in cases:
            data=copy.deepcopy(initial)
            row=next(r for r in data['material_declarations'] if r['name']==name)
            row['use_roles_draft'][role].remove(use)
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'Missing reviewed metric semantic role'):
                run_check({manifest_key:encoded(data)})

    def test_importer_fixtures_cannot_be_omitted_or_retargeted(self):
        data=copy.deepcopy(initial); data.pop('checked_bridge_importers')
        with self.assertRaisesRegex(ValueError,'Missing metric bridge importer fixtures'):
            run_check({manifest_key:encoded(data)})
        for name in ('ChallengeMaterialCheck','SolutionMaterialCheck'):
            data=copy.deepcopy(initial)
            next(x for x in data['checked_bridge_importers'] if x['module']==name)['parent']='OtherMaterial'
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'Invalid metric bridge importer mapping'):
                run_check({manifest_key:encoded(data)})

    def test_named_importer_markers_cannot_be_removed(self):
        for name in ('ChallengeMaterialCheck','SolutionMaterialCheck'):
            for contract in ('restricted_ae_instance','pair_filter_composition','derivative_at_nhds_instance'):
                for prefix in ('theorem ','#print axioms '):
                    data=copy.deepcopy(initial)
                    path=name+'.lean'
                    old=prefix+'MetricGraphMaterialImporterCheck.'+contract
                    changed=files[path].replace(old,prefix+'MetricGraphMaterialImporterCheck.removed_'+contract,1)
                    self.assertNotEqual(changed,files[path])
                    next(x for x in data['checked_bridge_importers'] if x['module']==name)['sha256']=sha(changed.encode())
                    with self.subTest(name=name,contract=contract,prefix=prefix),self.assertRaisesRegex(ValueError,'Missing metric bridge importer composition'):
                        run_check({manifest_key:encoded(data),path:changed})

    def test_named_parent_contract_markers_cannot_be_removed(self):
        contracts=('ae_measure_null_contract','filter_tendsto_contract','filter_map_membership_contract',
                   'filter_tendsto_preimage_contract','nhds_within_contract','nhds_open_sets_contract',
                   'mem_nhds_open_contract','derivative_at_nhds_contract','quotient_map_continuity_contract','quotient_topology_contract',
                   'graph_quotient_topology_contract','complex_sine_contract','complex_cosine_contract')
        for module in ('ChallengeMaterial','SolutionMaterial'):
            for name in contracts:
                for prefix in ('theorem ','#print axioms '):
                    data=copy.deepcopy(initial)
                    path=module+'.lean'
                    changed=files[path].replace(prefix+name,prefix+'removed_'+name,1)
                    self.assertNotEqual(changed,files[path])
                    next(x for x in data['checked_bridge_modules'] if x['module']==module)['sha256']=sha(changed.encode())
                    with self.subTest(module=module,name=name,prefix=prefix),self.assertRaisesRegex(ValueError,'Bridge missing named contract'):
                        run_check({manifest_key:encoded(data),path:changed})

    def test_known_block_comment_false_positive_is_not_semantic_validation(self):
        data=copy.deepcopy(initial)
        path='ChallengeMaterialCheck.lean'
        marker='public import ChallengeMaterial\n'
        self.assertEqual(files[path].count(marker),1)
        changed=files[path].replace(marker,marker+'\n/-\n',1)+'\n-/\n'
        next(x for x in data['checked_bridge_importers'] if x['module']=='ChallengeMaterialCheck')['sha256']=sha(changed.encode())
        # This documents a deliberate structural-check limitation; a real
        # Lean importer/axiom negative control must reject the missing output.
        self.assertEqual(run_check({manifest_key:encoded(data),path:changed})['status'],'pass')


if __name__ == '__main__':
    unittest.main()
