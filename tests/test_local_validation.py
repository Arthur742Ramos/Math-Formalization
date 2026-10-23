"""Protect the migration's exact workflow inventory and local coverage."""
import hashlib
import json
from pathlib import Path
import subprocess
import unittest
import yaml

ROOT = Path(__file__).resolve().parents[1]


class LocalMigrationTests(unittest.TestCase):
    def test_every_retired_definition_is_preserved_exactly_and_inactive(self):
        inventory = json.loads((ROOT / 'validation/workflow-inventory.json').read_text())
        base = inventory['base_commit']
        original = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', base, '.github/workflows'], cwd=ROOT, text=True).splitlines()
        entries = inventory['workflows']
        self.assertEqual({Path(f).name for f in original}, {e['file'] for e in entries})
        self.assertEqual(56, len(entries))
        self.assertFalse(list((ROOT / '.github/workflows').glob('*.y*ml')))
        for e in entries:
            with self.subTest(workflow=e['file']):
                old = subprocess.check_output(['git', 'show', base + ':.github/workflows/' + e['file']], cwd=ROOT)
                archived = (ROOT / 'validation/retired-workflows' / e['file']).read_bytes()
                self.assertEqual(old, archived)
                self.assertEqual(hashlib.sha256(old).hexdigest(), e['sha256'])

    def test_native_validation_commands_survive_and_parse_as_bash(self):
        entries = json.loads((ROOT / 'validation/workflow-inventory.json').read_text())['workflows']
        for e in entries:
            if e['kind'] != 'native':
                continue
            original = yaml.safe_load((ROOT / 'validation/retired-workflows' / e['file']).read_bytes())
            local = '\n'.join(e['local_commands'])
            self.assertNotIn('${{', local)
            self.assertNotIn('sudo ', local)
            self.assertNotIn('elan-init', local)
            for job in original['jobs'].values():
                for step in job.get('steps', []):
                    if 'run' not in step or 'elan-init' in step['run']:
                        continue
                    for line in step['run'].splitlines():
                        if not line.strip().startswith('elan toolchain install '):
                            self.assertIn(line, local, (e['file'], step.get('name')))
            for command in e['local_commands']:
                subprocess.run(['bash', '-n'], input=command, text=True, check=True)

    def test_package_trees_and_historical_records_are_unchanged(self):
        base = json.loads((ROOT / 'validation/workflow-inventory.json').read_text())['base_commit']
        changed = subprocess.check_output(['git', 'diff', '--name-only', base, 'HEAD', '--', 'topology', 'REGISTRATIONS.json', 'READINESS.json', 'PREPARATIONS.json', 'catalog-evidence'], cwd=ROOT, text=True)
        self.assertEqual('', changed)

    def test_canonical_cli_preserves_capacity_and_report_gates(self):
        source = (ROOT / 'scripts/local_canonical.py').read_text()
        self.assertIn("'check-capacity'", source)
        self.assertIn("'status') == 'pass'", source)
        self.assertNotIn('sudo', source)
        self.assertNotIn('install_bwrap', source)


if __name__ == '__main__':
    unittest.main()
