"""Focused generated-sum and real-volume provenance controls; no Lean build."""
import copy
import hashlib
import json
import pathlib
import sys
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'computational-hodge/metric-graph-resonance'
sys.path.insert(0, str(ROOT / 'scripts'))
import check_imported_definitions as checker


class GeneratedAndVolumeEvidence(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((PROJECT / 'verification/material-imported-definitions.json').read_text(encoding='utf8'))
        self.rows = {r['name']: r for r in self.data['material_declarations']}
        self.excerpts = {e['name']: (s, e) for s in self.data['source_files'] for e in s['excerpts']}
        self.sum_source, self.sum_excerpt = self.excerpts['Finset.sum generated producer']
        self.vol_source, self.vol_excerpt = self.excerpts['real_Lebesgue_volume']
        self.dep = self.data['dependency']

    def test_actual_draft_static_consistency_only(self):
        result = checker.check(PROJECT)
        self.assertEqual(result['upstream_origin'], 'not-checked')
        self.assertIn('Finset.sum', result['material_declarations'])
        self.assertIn('Real.volume_eq_stieltjes_id', result['material_declarations'])
        self.assertIn('separate actual Lean build required', result['bridge_compilation'])

    def test_valid_pinned_contract_helpers(self):
        checker.check_generated_sum_kind('Finset.sum', 'generated_additive', 2)
        checker.check_real_volume_kind('Real.volume_eq_stieltjes_id', 'theorem', 2)
        checker.check_pinned_generated_sum(self.rows['Finset.sum'], self.dep, self.sum_source, self.sum_excerpt)
        checker.check_pinned_real_volume(self.rows['Real.volume_eq_stieltjes_id'], self.dep, self.vol_source, self.vol_excerpt)
        checker.check_pinned_real_ae(*self.excerpts['AE_null_complement_contract'])

    def test_altered_ae_source_fails(self):
        for index, key, value in [(0, 'path', 'Mathlib/Other.lean'),
                                  (0, 'sha256', '0' * 64),
                                  (1, 'sha256', '0' * 64), (1, 'first_line', 1)]:
            args = copy.deepcopy(self.excerpts['AE_null_complement_contract'])
            args[index][key] = value
            with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                checker.check_pinned_real_ae(*args)

    def test_wrong_kinds_names_and_downgrades_fail(self):
        for name,kind,version in [('Finset.sum','def',1),('Finset.sum','def',2),('Other.sum','generated_additive',2)]:
            with self.subTest(name=name,kind=kind,version=version), self.assertRaises(ValueError):
                checker.check_generated_sum_kind(name,kind,version)
        for kind,version in [('def',1),('def',2)]:
            with self.subTest(kind=kind,version=version), self.assertRaises(ValueError):
                checker.check_real_volume_kind('Real.volume_eq_stieltjes_id',kind,version)

    def test_altered_producer_pin_and_source_fail(self):
        cases = [(0,'producer','Other.prod'),(0,'bridge_kind','literal-unfolding'),
                 (1,'commit','0'*40),(2,'path','Mathlib/Other.lean'),
                 (2,'sha256','0'*64),(2,'git_blob_sha1','0'*40),
                 (3,'first_line',60),(3,'sha256','0'*64),
                 (3,'text',self.sum_excerpt['text'].replace('@[to_additive','@[other'))]
        for index,key,value in cases:
            args=copy.deepcopy([self.rows['Finset.sum'],self.dep,self.sum_source,self.sum_excerpt])
            args[index][key]=value
            with self.subTest(index=index,key=key), self.assertRaises(ValueError):
                checker.check_pinned_generated_sum(*args)

    def test_altered_volume_pin_and_source_fail(self):
        cases = [(0,'bridge_kind','literal-unfolding'),(1,'commit','0'*40),
                 (2,'path','Mathlib/Other.lean'),(2,'sha256','0'*64),
                 (3,'first_line',55),(3,'sha256','0'*64),
                 (3,'text',self.vol_excerpt['text'].replace('volume_eq_stieltjes_id','wrong_name'))]
        for index,key,value in cases:
            args=copy.deepcopy([self.rows['Real.volume_eq_stieltjes_id'],self.dep,self.vol_source,self.vol_excerpt])
            args[index][key]=value
            with self.subTest(index=index,key=key), self.assertRaises(ValueError):
                checker.check_pinned_real_volume(*args)

    def test_full_check_rejects_kind_spoofs(self):
        files={p.relative_to(PROJECT).as_posix():p.read_text(encoding='utf8')
               for p in PROJECT.rglob('*') if p.is_file()}
        class MemoryFile:
            def __init__(self, value): self.value=value
            def read_text(self): return self.value
            def read_bytes(self): return self.value.encode()
        def local_file(_root,name):
            if name not in files:raise ValueError('missing synthetic file')
            return MemoryFile(files[name])
        for name,expected in [('Finset.sum','Unsupported generated-additive name or declaration kind'),
                              ('Real.volume_eq_stieltjes_id','Real-volume contract requires pinned theorem evidence')]:
            modified=copy.deepcopy(self.data)
            next(r for r in modified['material_declarations'] if r['name']==name)['declaration_kind']='def'
            files['verification/material-imported-definitions.json']=json.dumps(modified,ensure_ascii=False)
            with self.subTest(name=name),patch.object(checker,'local_file',side_effect=local_file),self.assertRaisesRegex(ValueError,expected):
                checker.check(PROJECT)

    def test_bridge_contract_and_axiom_marker_removal_fails(self):
        files = {p.relative_to(PROJECT).as_posix(): p.read_text(encoding='utf8')
                 for p in PROJECT.rglob('*') if p.is_file()}
        class MemoryFile:
            def __init__(self, value): self.value = value
            def read_text(self): return self.value
            def read_bytes(self): return self.value.encode()
        def local_file(_root, name):
            if name not in files: raise ValueError('missing synthetic file')
            return MemoryFile(files[name])
        for module in self.data['checked_bridge_modules']:
            for name in ('generated_sum_contract', 'finite_univ_sum_contract',
                         'real_volume_contract', 'ae_real_volume_contract'):
                for prefix in ('theorem ', '#print axioms '):
                    with self.subTest(module=module['path'], contract=name, prefix=prefix):
                        path = module['path']
                        original = files[path]
                        mutated = original.replace(prefix + name, prefix + 'removed_' + name, 1)
                        self.assertNotEqual(mutated, original)
                        files[path] = mutated
                        data = copy.deepcopy(self.data)
                        target = next(x for x in data['checked_bridge_modules'] if x['path'] == path)
                        target['sha256'] = hashlib.sha256(mutated.encode()).hexdigest()
                        files['verification/material-imported-definitions.json'] = json.dumps(data, ensure_ascii=False)
                        with patch.object(checker, 'local_file', side_effect=local_file), \
                                self.assertRaisesRegex(ValueError, 'Bridge missing named contract'):
                            checker.check(PROJECT)
                        files[path] = original


if __name__ == '__main__':
    unittest.main()
