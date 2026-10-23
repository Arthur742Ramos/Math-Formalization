"""Synthetic gate tests only: no canonical, renderer, build or installer runs."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

D = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('inert_report_gate', D / 'report_gate.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
plan = json.loads((D / 'plan.json').read_text())
# Reuse only the pinned report schema shape; this mutated fixture is NOT verification evidence.
prior = D.parents[1] / 'sierpinski-rationals-2026-10-23/canonical/full-report.json'
url = 'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/123456789'


def synthetic():
    r = copy.deepcopy(json.loads(prior.read_text()))
    r['source'].update(repository=plan['repository'], commit=plan['source_commit'], project_path=plan['project_path'])
    r['workflow_url'] = url
    r['submission']['submission_id'] = plan['request_id']
    for key, name in [('challenge','LEChallenge.lean'),('solution','LESolution.lean'),
                      ('comparator','comparator.json'),('formalization','formalization.yaml'),
                      ('lakefile','lakefile.toml'),('lake_manifest','lake-manifest.json')]:
        r[key].update(path=plan['project_path']+'/'+name, sha256=plan['source_files_sha256'][name])
    r['challenge']['module'] = 'LEChallenge'
    r['solution']['module'] = 'LESolution'
    r['comparator'].update(challenge_module='LEChallenge', solution_module='LESolution')
    for key in ['theorem_names','definition_names','permitted_axioms']:
        r['comparator'][key] = plan[key]
    c=json.loads(r['protected_config']);c['solution_module']='LESolution'
    for key in ['theorem_names','definition_names','permitted_axioms']:c[key]=plan[key]
    r['protected_config']=json.dumps(c,indent=2)+'\n'
    r['protected_config_sha256']=hashlib.sha256(r['protected_config'].encode()).hexdigest()
    return r


class SyntheticGate(unittest.TestCase):
    def test_schema_compatible_synthetic_fixture(self):
        gate.authenticate_fields(plan, synthetic(), url, 1)

    def test_rejects_wrong_or_incomplete_evidence(self):
        mutations = [
            ('not_pass',lambda r:r.update(status='fail')),
            ('errors',lambda r:r.update(errors=['failure'])),
            ('incomplete',lambda r:r.update(stage='prepare')),
            ('wrong_source',lambda r:r['source'].update(commit='0'*40)),
            ('wrong_repository',lambda r:r['source'].update(repository='other/repo')),
            ('wrong_project',lambda r:r['source'].update(project_path='topology/other')),
            ('wrong_run',lambda r:r.update(workflow_url=url+'9')),
            ('wrong_request',lambda r:r['submission'].update(submission_id='other')),
            ('wrong_toolchain',lambda r:r.update(lean_toolchain='leanprover/lean4:v4.36.0')),
            ('wrong_profile',lambda r:r.update(execution_profile='palomar-namespace-16x32-v1')),
            ('wrong_profile_hash',lambda r:r['verification_profile'].update(sha256='0'*64)),
            ('wrong_metadata',lambda r:r['formalization'].update(sha256='0'*64)),
            ('wrong_comparator',lambda r:r['comparator'].update(sha256='0'*64)),
            ('wrong_challenge',lambda r:r['challenge'].update(sha256='0'*64)),
            ('wrong_lockfile',lambda r:r['lake_manifest'].update(sha256='0'*64)),
            ('wrong_selection',lambda r:r['comparator'].update(theorem_names=[])),
            ('wrong_protected_hash',lambda r:r.update(protected_config_sha256='0'*64)),
            ('missing_kernels',lambda r:r.update(kernels=[])),
            ('failed_conron',lambda r:r['kernel_attempts'][0].update(exit_code=1)),
            ('wrong_mathlib',lambda r:r.update(project_dependencies=[])),
        ]
        for name, mutate in mutations:
            with self.subTest(name=name):
                r=synthetic();mutate(r)
                with self.assertRaises(ValueError):gate.authenticate_fields(plan,r,url,1)

    def test_rejects_workflow_rerun(self):
        with self.assertRaises(ValueError):gate.authenticate_fields(plan,synthetic(),url,2)

    def test_inert_template_structure_and_pins(self):
        import yaml
        p=D/'canonical-pair.yml.inert';s=p.read_text();y=yaml.load(s,Loader=yaml.BaseLoader)
        self.assertEqual(y['on'],{'push':{'branches':[plan['activation_branch']], 'paths':[plan['activation_target']]}})
        self.assertEqual(y['permissions'],{'contents':'read'})
        self.assertEqual(set(y['jobs']),{'full','authenticate','render'})
        self.assertEqual(y['jobs']['full']['uses'],plan['pipeline_repository']+'/.github/workflows/submission.yml@'+plan['pipeline_commit'])
        self.assertEqual(y['jobs']['full']['with']['commit'],plan['source_commit'])
        self.assertEqual(y['jobs']['full']['with']['execution_profile'],'palomar-standard-v1')
        self.assertEqual(y['jobs']['render']['needs'],'authenticate')
        self.assertIn("render_allowed == 'true'",y['jobs']['render']['if'])
        self.assertNotIn('--inadvisably-no-sandbox',s)
        self.assertNotIn('sysctl -w',s)
        self.assertFalse((D.parents[2]/plan['activation_target']).exists())
        self.assertEqual(plan['current_hosted_runs_started'],0)


if __name__=='__main__':unittest.main(verbosity=2)
