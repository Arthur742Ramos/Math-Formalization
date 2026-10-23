"""Inert-plan report authenticator. Executing it does not launch any verification.

A renderer may be released only after the caller has downloaded the full report
from THIS workflow run, checked the reusable job succeeded, and invoked this
script against exact checked-out source and pipeline Git objects. Synthetic
unit fixtures are not canonical reports and confer no run authorization.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def authenticate_fields(plan, report, workflow_url, run_attempt):
    require(run_attempt == 1, 'rerun is outside the single-attempt plan')
    require(report.get('status') == 'pass' and not report.get('errors'), 'full report did not pass')
    require(report.get('schema_version') == 2 and report.get('stage') == 'complete'
            and report.get('phase') == 'verification', 'not a completed full verification report')
    source = report.get('source', {})
    require(source.get('repository') == plan['repository'] and
            source.get('commit') == plan['source_commit'] and
            source.get('project_path') == plan['project_path'], 'wrong full source')
    require(report.get('workflow_url') == workflow_url, 'report came from another workflow run')
    require(report.get('submission', {}).get('submission_id') == plan['request_id'], 'wrong request id')
    require(report.get('lean_toolchain') == plan['toolchain'] and
            report.get('toolchain_commit') == plan['toolchain_commit'], 'wrong toolchain')
    require(report.get('execution_profile') == plan['execution_profile'], 'wrong execution profile')
    profile = report.get('verification_profile', {})
    expected = plan['verification_profile']
    require(profile.get('id') == expected['id'] and
            profile.get('sha256') == plan['verification_profile_sha256'] and
            profile.get('runner') == expected['runner'] and
            profile.get('limits') == expected['limits'] and
            profile.get('trusted_tools') == expected['trusted_tools'], 'profile binding mismatch')
    require(report.get('bwrap_source_tag') == 'v0.12.0', 'wrong bubblewrap release')
    package = plan['project_path']
    for key, name in [('challenge', 'LEChallenge.lean'), ('solution', 'LESolution.lean'),
                      ('comparator', 'comparator.json'), ('formalization', 'formalization.yaml'),
                      ('lakefile', 'lakefile.toml'), ('lake_manifest', 'lake-manifest.json')]:
        value = report.get(key, {})
        require(value.get('path') == package + '/' + name and
                value.get('sha256') == plan['source_files_sha256'][name], 'wrong ' + key + ' bytes')
    config = report['comparator']
    for key in ['theorem_names', 'definition_names', 'permitted_axioms']:
        require(config.get(key) == plan[key], 'wrong selected ' + key)
    require(config.get('challenge_module') == 'LEChallenge' and
            config.get('solution_module') == 'LESolution', 'wrong contract entrypoints')
    raw_protected = report.get('protected_config', '')
    require(isinstance(raw_protected, str) and
            digest(raw_protected.encode()) == report.get('protected_config_sha256'), 'unbound protected config')
    protected = json.loads(raw_protected)
    for key in ['theorem_names', 'definition_names', 'permitted_axioms']:
        require(protected.get(key) == plan[key], 'wrong protected ' + key)
    require(protected.get('solution_module') == 'LESolution', 'wrong protected solution')
    require(re.fullmatch(r'PalomarCanonical[0-9a-f]+\.Challenge', protected.get('challenge_module', '')),
            'wrong protected Challenge namespace')
    require(re.fullmatch(r'[0-9a-f]{64}', report['challenge'].get('canonical_olean_sha256', '')),
            'missing canonical Challenge identity')
    deps = report.get('project_dependencies', [])
    require(any(d.get('repository') == 'leanprover-community/mathlib4' and
                d.get('revision') == plan['mathlib_commit'] for d in deps), 'wrong Mathlib pin')
    kernels = report.get('kernels', [])
    require({k.get('name') for k in kernels} == {'nanoda', 'con-ron'}, 'missing independent kernels')
    con_ron = next(k for k in kernels if k.get('name') == 'con-ron')
    require('--jobs=2' in con_ron.get('argv', []) and '--verified' in con_ron.get('argv', []),
            'wrong con-ron verification or worker mode')
    require(any(k.get('name') == 'con-ron' and k.get('status') == 'accepted' and
                k.get('exit_code') == 0 for k in report.get('kernel_attempts', [])), 'con-ron did not accept')


def authenticate_checkouts(plan, source, pipeline):
    git = lambda root, *args: subprocess.check_output(['git', '-C', str(root), *args]).decode().strip()
    require(git(source, 'rev-parse', 'HEAD') == plan['source_commit'], 'wrong source checkout')
    require(git(source, 'rev-parse', 'HEAD:' + plan['project_path']) == plan['source_package_tree'],
            'wrong source package tree')
    require(git(pipeline, 'rev-parse', 'HEAD') == plan['pipeline_commit'], 'wrong pipeline checkout')
    package = source / plan['project_path']
    for name, expected in plan['source_files_sha256'].items():
        p = package / name
        require(p.is_file() and not p.is_symlink() and digest(p.read_bytes()) == expected,
                'source checkout bytes changed: ' + name)
    for name, expected in plan['pipeline_files_sha256'].items():
        p = pipeline / name
        require(p.is_file() and not p.is_symlink() and digest(p.read_bytes()) == expected,
                'pipeline checkout bytes changed: ' + name)
    archive = subprocess.check_output(['git', '-C', str(source), 'archive', '--format=tar',
                                       plan['source_commit'], plan['project_path']])
    require(len(archive) == plan['source_archive']['bytes'] and
            digest(archive) == plan['source_archive']['sha256'], 'wrong source archive bytes')
    return archive


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--plan', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--source-checkout', type=Path, required=True)
    p.add_argument('--pipeline-checkout', type=Path, required=True)
    p.add_argument('--workflow-url', required=True)
    p.add_argument('--workflow-head', required=True)
    p.add_argument('--run-attempt', type=int, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    require(a.plan.is_file() and a.plan.stat().st_size < 512 * 1024, 'unbounded plan')
    require(a.report.is_file() and not a.report.is_symlink() and a.report.stat().st_size < 2 * 1024 * 1024,
            'unbounded or nonregular report')
    plan = json.loads(a.plan.read_text())
    require(re.fullmatch(r'[0-9a-f]{40}', a.workflow_head), 'invalid workflow head')
    require(re.fullmatch(r'https://github\.com/Arthur742Ramos/Math-Formalization/actions/runs/[0-9]+',
                         a.workflow_url), 'invalid workflow URL')
    report = json.loads(a.report.read_text())
    receipt = dict(status='fail', scope='same-run full-report/source/pipeline authentication; not an approval',
                   workflow_url=a.workflow_url, workflow_head=a.workflow_head, run_attempt=a.run_attempt,
                   source_commit=plan['source_commit'], source_package_tree=plan['source_package_tree'],
                   pipeline_commit=plan['pipeline_commit'], report_sha256=digest(a.report.read_bytes()),
                   plan_sha256=digest(a.plan.read_bytes()))
    try:
        authenticate_fields(plan, report, a.workflow_url, a.run_attempt)
        archive = authenticate_checkouts(plan, a.source_checkout, a.pipeline_checkout)
        a.output.with_suffix('.source.tar').write_bytes(archive)
        receipt.update(status='pass', source_archive=plan['source_archive'],
                       metadata_sha256=plan['source_files_sha256']['formalization.yaml'],
                       comparator_sha256=plan['source_files_sha256']['comparator.json'])
    except Exception as e:
        receipt['error'] = str(e)
        a.output.write_text(json.dumps(receipt, indent=2) + '\n')
        raise
    a.output.write_text(json.dumps(receipt, indent=2) + '\n')
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
            f.write('render_allowed=true\n')


if __name__ == '__main__':
    main()
