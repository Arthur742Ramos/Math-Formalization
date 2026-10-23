#!/usr/bin/env python3
"""Run bounded local checks and retain commit-bound receipts outside the source."""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'validation/workflow-inventory.json'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def run(command, cwd, env, log, seconds):
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            return 124


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target', help='catalog or a native workflow filename from the inventory')
    parser.add_argument('--plan', action='store_true', help='print commands without running them')
    parser.add_argument('--seconds', type=int, default=600, help='total wall-clock budget (max 7200)')
    parser.add_argument('--lock', default='/home/formalization/workloads/.heavy-verification.lock')
    args = parser.parse_args()
    entries = json.loads(MANIFEST.read_text())['workflows']
    if args.target == 'catalog':
        commands = [('root', 'python3 scripts/check_catalog.py --package-checks'),
                    ('root', 'python3 -m unittest discover -s tests -v')]
        for name in ['kuratowski-ulam', 'locally-compact-baire', 'banach-mazur-baire',
                     'banach-mazur-category', 'strong-choquet-polish']:
            commands.append(('root', 'python3 scripts/check_imported_definitions.py --project-path topology/' + name))
        commands.append(('root', 'python3 scripts/check_release_packet.py --project-path topology/collectionwise-normal '
                         '--commit ' + git('rev-parse', 'HEAD') + ' --historical-report '
                         'catalog-evidence/collectionwise-2026-10-18/full-report.json'))
    else:
        entry = next((e for e in entries if e['file'] == args.target), None)
        if not entry or entry['kind'] != 'native':
            parser.error('use a native inventory entry; canonical full/render commands are in LOCAL-VALIDATION.md')
        commands = [(entry['directory'], c) for c in entry['local_commands']]
    if args.plan:
        print(json.dumps(commands, indent=2))
        return 0
    if os.geteuid() == 0:
        parser.error('project checks must run as a non-root user')
    if not 1 <= args.seconds <= 7200:
        parser.error('--seconds must be between 1 and 7200')
    if git('status', '--porcelain', '--untracked-files=all'):
        parser.error('commit all source changes first; receipts must bind a clean source')
    import time
    with open(args.lock, 'a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            parser.error('shared verification lock is busy; coordinate with its owner')
        evidence = Path(git('rev-parse', '--absolute-git-dir')) / 'local-validation'
        evidence.mkdir(exist_ok=True)
        receipt_dir = Path(tempfile.mkdtemp(prefix='run-', dir=evidence))
        env = dict(os.environ, RUNNER_TEMP=str(receipt_dir), GITHUB_WORKSPACE=str(ROOT))
        receipt = {'commit': git('rev-parse', 'HEAD'), 'tree': git('rev-parse', 'HEAD^{tree}'),
                   'target': args.target, 'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'scope': 'Local commands only; not independent review, canonical full verification or registry intake.',
                   'steps': [], 'status': 'running'}
        deadline = time.monotonic() + args.seconds
        try:
            for index, (directory, command) in enumerate(commands):
                log = receipt_dir / f'{index:02d}.log'
                remaining = int(deadline - time.monotonic())
                code = run(['bash', '-euo', 'pipefail', '-c', command],
                           ROOT if directory == 'root' else ROOT / directory, env, log, max(1, remaining)) if remaining > 0 else 124
                step = {'command': command, 'directory': directory, 'exit_code': code}
                if log.exists():
                    step.update(log=log.name, sha256=hashlib.sha256(log.read_bytes()).hexdigest())
                receipt['steps'].append(step)
                print(f'{index + 1}/{len(commands)} exit={code}: {command.splitlines()[0]}', flush=True)
                if code:
                    receipt['status'] = 'fail'
                    break
            else:
                receipt['status'] = 'pass'
            if git('status', '--porcelain', '--untracked-files=all') or git('rev-parse', 'HEAD') != receipt['commit']:
                receipt['status'] = 'fail'
                receipt['source_changed'] = True
        finally:
            receipt['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
            (receipt_dir / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
            print(receipt_dir / 'receipt.json', flush=True)
        return 0 if receipt['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
