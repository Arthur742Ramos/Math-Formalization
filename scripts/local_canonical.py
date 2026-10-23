#!/usr/bin/env python3
"""Invoke an already installed pinned canonical verifier locally, without setup."""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
from local_validate import run


def report_passes(report, fields):
    source = report.get('source', {})
    return (report.get('status') == 'pass'
            and source.get('repository') == fields['repository']
            and source.get('commit') == fields['commit'])


def load_report(path):
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 2 * 1024 * 1024:
        raise ValueError('canonical report must be a regular file of at most 2 MiB')
    report = json.loads(path.read_text())
    if not isinstance(report, dict):
        raise ValueError('canonical report must be an object')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['full', 'render'])
    p.add_argument('--pipeline', type=Path, required=True)
    p.add_argument('--pipeline-commit', required=True)
    p.add_argument('--inputs', type=Path, required=True,
                   help='canonical event JSON (full), or renderer prepare argument object (render)')
    p.add_argument('--bwrap', type=Path, required=True)
    p.add_argument('--evidence-root', type=Path, required=True)
    p.add_argument('--seconds', type=int, required=True)
    p.add_argument('--lock', default='/home/formalization/workloads/.heavy-verification.lock')
    a = p.parse_args()
    if os.geteuid() == 0 or not 1 <= a.seconds <= 7200:
        p.error('run non-root with a wall-clock budget of 1..7200 seconds')
    pipeline = a.pipeline.resolve()
    if not re.fullmatch('[0-9a-f]{40}', a.pipeline_commit):
        p.error('pin the full pipeline commit')
    def git(*args):
        return subprocess.check_output(['git', '-C', str(pipeline), *args], text=True).strip()
    if git('rev-parse', 'HEAD') != a.pipeline_commit or git('status', '--porcelain', '--untracked-files=all'):
        p.error('pipeline must be clean at the exact reviewed revision, with dependencies installed outside its source')
    if not a.bwrap.resolve().is_file() or not os.access(a.bwrap.resolve(), os.X_OK):
        p.error('provide an existing authenticated executable bubblewrap; no installer is run')
    bwrap_digest = hashlib.sha256(a.bwrap.resolve().read_bytes()).hexdigest()
    inputs_bytes = a.inputs.read_bytes()
    inputs = json.loads(inputs_bytes)
    if a.mode == 'full':
        fields = inputs['inputs']
        if (fields.get('repository') != 'Arthur742Ramos/Math-Formalization'
                or fields.get('mode') != 'full'
                or fields.get('pipeline_commit') != a.pipeline_commit
                or fields.get('execution_profile') != 'palomar-standard-v1'
                or not re.fullmatch('[0-9a-f]{40}', fields.get('commit', ''))):
            p.error('full inputs must bind this repository, exact source and pipeline, full mode and standard profile')
    else:
        fields = inputs
        required = {'repository', 'commit', 'challenge_sha256', 'project_path', 'challenge_path',
                    'solution_path', 'comparator_config_path', 'lakefile_path', 'lean_toolchain_path'}
        if (set(fields) != required or fields['repository'] != 'Arthur742Ramos/Math-Formalization'
                or not re.fullmatch('[0-9a-f]{40}', fields['commit'])):
            p.error('render inputs must contain exactly the documented prepare fields and immutable source')
    a.evidence_root.mkdir(parents=True, exist_ok=True)
    with open(a.lock, 'a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            p.error('shared verification lock is busy')
        evidence = Path(tempfile.mkdtemp(prefix=a.mode + '-', dir=a.evidence_root.resolve()))
        work = evidence / 'work'
        report = evidence / 'report.json'
        env = dict(os.environ, PALOMAR_EXECUTION_PROFILE='palomar-standard-v1',
                   PALOMAR_JOB_STARTED_AT=str(int(time.time())), RUNNER_TEMP=str(evidence),
                   BUNDLE_GEMFILE=str(pipeline / 'Gemfile'))
        common = ['--work-dir', str(work), '--output', str(report)]
        python = shutil.which('python3')
        if a.mode == 'full':
            bundle = shutil.which('bundle')
            if not bundle:
                p.error('canonical licensee dependencies must already be installed')
            event = evidence / 'inputs.json'
            event.write_bytes(inputs_bytes)
            script = str(pipeline / 'scripts/verify_submission.py')
            commands = [[python, script, 'prepare', '--event', str(event), *common, '--licensee', bundle],
                        [python, script, 'check-capacity', '--disk-path', str(evidence), '--output', str(report)],
                        [python, script, 'execute', *common, '--bwrap', str(a.bwrap.resolve()),
                         '--bwrap-source-tag', 'v0.12.0', '--execution-budget-seconds', str(a.seconds),
                         '--workflow-url', evidence.as_uri()]]
        else:
            prepare = [python, '-m', 'scripts.render_challenge', 'prepare', *common]
            for key, value in fields.items():
                prepare.extend(['--' + key.replace('_', '-'), str(value)])
            commands = [prepare, [python, '-m', 'scripts.render_challenge', 'execute', *common,
                        '--bwrap', str(a.bwrap.resolve()), '--bwrap-source-tag', 'v0.12.0',
                        '--renderer-commit', a.pipeline_commit, '--workflow-url', evidence.as_uri()]]
        receipt = {'mode': a.mode, 'repository': fields['repository'], 'commit': fields['commit'],
                   'pipeline_commit': a.pipeline_commit, 'inputs_sha256': hashlib.sha256(inputs_bytes).hexdigest(),
                   'bwrap_sha256': bwrap_digest,
                   'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'scope': 'Local canonical preflight; no registry intake or acceptance.', 'steps': [], 'status': 'error'}
        deadline = time.monotonic() + a.seconds
        try:
            for i, command in enumerate(commands):
                log = evidence / f'{i:02d}.log'
                remaining = int(deadline - time.monotonic())
                code = run(command, pipeline, env, log, remaining) if remaining > 0 else 124
                step = {'argv': command, 'exit_code': code}
                if log.exists():
                    step.update(log=log.name, sha256=hashlib.sha256(log.read_bytes()).hexdigest())
                receipt['steps'].append(step)
                if code or not report.exists():
                    break
                observed = load_report(report)
                if observed.get('status') in {'fail', 'error'}:
                    break
            else:
                if report_passes(load_report(report), fields):
                    receipt['status'] = 'pass'
            if (git('rev-parse', 'HEAD') != a.pipeline_commit
                    or git('status', '--porcelain', '--untracked-files=all')
                    or hashlib.sha256(a.bwrap.resolve().read_bytes()).hexdigest() != bwrap_digest):
                receipt['status'] = 'error'
                receipt['tool_source_changed'] = True
            if report.exists():
                receipt['report_sha256'] = hashlib.sha256(report.read_bytes()).hexdigest()
        finally:
            receipt['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
            (evidence / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
            print(evidence / 'receipt.json')
        return 0 if receipt['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
