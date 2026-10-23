"""Protect the migration's exact workflow inventory and local coverage."""
import hashlib
import json
from pathlib import Path
import subprocess
import unittest
import yaml
import sys

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

    def test_canonical_report_gate_rejects_failed_pending_and_wrong_source(self):
        sys.path.insert(0, str(ROOT / 'scripts'))
        import local_canonical
        fields = {'repository': 'Arthur742Ramos/Math-Formalization', 'commit': 'a' * 40}
        good = {'status': 'pass', 'source': dict(fields)}
        self.assertTrue(local_canonical.report_passes(good, fields))
        for status in ['fail', 'error', 'pending', None]:
            self.assertFalse(local_canonical.report_passes(dict(good, status=status), fields))
        for report in [{}, {'status': 'pass'}, dict(good, source=dict(fields, commit='b' * 40)),
                       dict(good, source=dict(fields, repository='another/repository'))]:
            self.assertFalse(local_canonical.report_passes(report, fields))

    def test_canonical_report_reader_rejects_symlink_and_oversize(self):
        import tempfile
        sys.path.insert(0, str(ROOT / 'scripts'))
        import local_canonical
        with tempfile.TemporaryDirectory() as temporary:
            report = Path(temporary) / 'report.json'
            report.write_text('{}')
            link = Path(temporary) / 'link.json'
            link.symlink_to(report)
            with self.assertRaises(ValueError):
                local_canonical.load_report(link)
            report.write_bytes(b' ' * (2 * 1024 * 1024 + 1))
            with self.assertRaises(ValueError):
                local_canonical.load_report(report)

    def test_timeout_kills_descendant_even_when_leader_exits_on_term(self):
        import os
        import signal
        import tempfile
        sys.path.insert(0, str(ROOT / 'scripts'))
        from local_validate import run
        code = ('import os,signal,time\n'
                'pid=os.fork()\n'
                'if pid==0:\n'
                ' signal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                ' print(os.getpid(),flush=True)\n'
                ' time.sleep(30)\n'
                'else: time.sleep(30)\n')
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / 'timeout.log'
            result = run([sys.executable, '-c', code], ROOT, dict(os.environ), log, 1)
            self.assertEqual(124, result)
            child = int(log.read_text().strip())
            try:
                state = Path(f'/proc/{child}/stat')
                if state.exists():
                    self.assertIn(state.read_text().split()[2], {'Z', 'X'})
            finally:
                try:
                    os.kill(child, signal.SIGKILL)
                except ProcessLookupError:
                    pass


if __name__ == '__main__':
    unittest.main()
