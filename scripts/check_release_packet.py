"""Check exact packaged status and full-report bindings before handing off fields.

Offline validation is not artifact authentication, editorial approval, permission
or duplicate/private-attempt clearance. Independently review report provenance.
"""
import argparse
import hashlib
import io
import json
import pathlib
import re
import subprocess
import tarfile
import tempfile

from check_imported_definitions import check as check_imported_definitions

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = 'Arthur742Ramos/Math-Formalization'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def snapshot(root, commit, project):
    require(re.fullmatch(r'[0-9a-f]{40}', commit), 'Use an exact source commit')
    require(re.fullmatch(r'topology/[a-z0-9-]+|algebraic-hodge/ddbar-pilot|computational-hodge/finite-periods|computational-hodge/presentation-homology|computational-hodge/geometric-descent|computational-hodge/geometric-obstruction|computational-hodge/loop-characters', project),
            'Invalid project path')
    def git(*args):
        return subprocess.check_output(['git', '-C', str(root), *args])
    paths = git('ls-tree', '-r', '--name-only', commit + ':' + project).decode().splitlines()
    require(paths, 'Source package is missing')
    return {name: git('show', commit + ':' + project + '/' + name) for name in paths}


def status_errors(files):
    """Reject the known stale completed-gate account; human review remains required."""
    stages = r'(?:canonical|protected Comparator|independent.kernel|NanoDa|con-ron|Challenge.rendering)'
    denial = (r'(?:remain(?:s)?\s+(?:separate\s+)?(?:outstanding|unperformed|unfulfilled|pending)|'
              r'have\s+not\s+run|has\s+not\s+run|(?:are|is)\s+(?:still\s+)?unperformed|'
              r'unperformed\s+(?:gates|at))')
    pattern = re.compile(stages + r'(?:(?![.!?;]|\n\s*\n).){0,350}?' + denial, re.I | re.S)
    errors = []
    for name in ['formalization.yaml', 'README.md', 'REVIEW.md', 'VERIFICATION.md', 'AUDIT.md', 'PLAN.md', 'RUN-PLAN.md']:
        if name not in files:
            continue
        text = files[name].decode().replace('**', '')
        for match in pattern.finditer(text):
            # Only an explicitly future-qualified subject is exempt. A mixed
            # full-verification/browser clause must not hide a stale full claim.
            future = re.search(r'\b(?:of|for)\s+(?:a\s+)?(?:later|another|new)\s+(?:source|commit)\b', match[0], re.I)
            if future and not re.search(r'\band\b', match[0][:future.start()], re.I):
                continue
            errors.append(name + ': stale blanket pending/completion account')
    return sorted(set(errors))


def check_kernel_account(report, protected):
    """Check legacy/current receipt consistency, not independent report authenticity.

    The current pinned pipeline requires Lean/NanoDa and records con-ron as an
    advisory replay. Historical protected configurations required both kernels.
    Actual artifact provenance and capacity authentication still need review.
    """
    required = set(protected['external_kernels'])
    names = [row['name'] for row in report['kernels']]
    require(len(names) == len(set(names)), 'Duplicate accepted kernel')
    accepted = set(names)
    log = report['comparator_log_tail']
    for message in ['nanoda kernel accepts the solution',
                    'Lean default kernel accepts the solution', 'Your solution is okay!']:
        require(message in log, 'Missing actual kernel/comparison acceptance')
    if required == {'nanoda', 'con-ron'}:
        require(accepted == required, 'Missing independent kernel')
        require('con-ron kernel accepts the solution' in log,
                'Missing actual kernel/comparison acceptance')
        return
    require(required == {'nanoda'} and accepted in ({'nanoda'}, {'nanoda', 'con-ron'}),
            'Unsupported protected kernel account')
    attempts = report.get('kernel_attempts', [])
    require(len(attempts) == 1 and attempts[0].get('name') == 'con-ron',
            'Missing advisory con-ron attempt')
    attempt = attempts[0]
    budget = attempt.get('budget_seconds')
    require(type(budget) is int and 0 <= budget <= 1800, 'Invalid advisory kernel budget')
    require(isinstance(attempt.get('detail'), str) and attempt['detail'].strip(),
            'Missing advisory kernel evidence')
    argv = attempt.get('argv', [])
    require(len(argv) == 3 and pathlib.PurePosixPath(argv[0]).name == 'con-ron'
            and re.fullmatch(r'--jobs=[1-9][0-9]*', argv[1]) and argv[2] == '--verified',
            'Advisory replay is not the verified-export invocation')
    require(isinstance(attempt.get('status'), str) and isinstance(attempt.get('reason'), str)
            and (attempt.get('exit_code') is None or type(attempt['exit_code']) is int),
            'Invalid advisory kernel result fields')
    outcome = (attempt.get('status'), attempt.get('reason'), attempt.get('exit_code'))
    if outcome == ('accepted', 'complete', 0):
        require(accepted == {'nanoda', 'con-ron'}, 'Accepted advisory kernel not recorded')
    else:
        require(outcome in {('declined', 'unsupported-inductive', 2),
                            ('declined', 'fuel-exhausted', 3),
                            ('declined', 'capacity', None)}, 'Unrecognized advisory kernel outcome')
        require(accepted == {'nanoda'}, 'Declined kernel incorrectly listed as accepted')
        warning = ('con-ron declined (' + attempt['reason'] +
                   '); mandatory Lean and NanoDa checks passed.')
        require(warning in report.get('warnings', []), 'Missing advisory decline warning')


def check_kernels(report, protected):
    """Require three accepted kernels under either retained canonical protocol.

    Current policy runs con-ron after mandatory protected comparison. A policy
    decline is not sufficient for this packet's stronger three-kernel claim.
    Artifact/caller authentication remains an independent release obligation.
    """
    configured = protected['external_kernels']
    kernels = report['kernels']
    require(len(kernels) == 2 and {k['name'] for k in kernels} == {'nanoda', 'con-ron'},
            'Missing or duplicate independent kernel')
    if set(configured) == {'nanoda', 'con-ron'}:
        require('con-ron kernel accepts the solution' in report['comparator_log_tail'],
                'Missing actual con-ron acceptance')
        return
    require(set(configured) == {'nanoda'} and report.get('schema_version') == 2 and
            report.get('phase') == 'verification', 'Unsupported protected kernel protocol')
    by_name = {k['name']: k['argv'] for k in kernels}
    require(by_name['nanoda'] == configured['nanoda'] and len(by_name['nanoda']) == 1 and
            pathlib.Path(by_name['nanoda'][0]).is_absolute() and
            pathlib.Path(by_name['nanoda'][0]).name == 'nanoda_bin', 'Wrong protected NanoDa command')
    attempts = report.get('kernel_attempts', [])
    require(len(attempts) == 1, 'Missing or duplicate con-ron replay')
    attempt = attempts[0]
    require(attempt['name'] == 'con-ron' and attempt['status'] == 'accepted' and
            attempt['reason'] == 'complete' and type(attempt['exit_code']) is int and
            attempt['exit_code'] == 0, 'con-ron replay did not accept')
    command = attempt['argv']
    require(command == by_name['con-ron'] and len(command) == 3 and
            pathlib.Path(command[0]).is_absolute() and pathlib.Path(command[0]).name == 'con-ron' and
            command[1:] == ['--jobs=2', '--verified'], 'Wrong verified con-ron replay command')
    require(type(attempt['budget_seconds']) is int and 1 <= attempt['budget_seconds'] <= 1800,
            'Invalid con-ron replay budget')
    lines = [line.strip() for line in attempt['detail'].splitlines() if line.strip()]
    accepted = r'con-ron: accepted [1-9][0-9]* declarations \(--verified\)(?: t=[0-9.]+s)?'
    modelled = (r'con-ron: [1-9][0-9]* inductive blocks modelled in-process: [^\n]+ '
                r'\([1-9][0-9]* generated records, checked by the fold as declarations '
                r'and not counted as records of the file\)')
    # The pinned verified checker can report these two Nat declarations being
    # ordered before the primitive operations they ground. This is diagnostic
    # metadata, never a substitute for its unique successful verdict below.
    hoisted = ('con-ron: 2 declarations hoisted ahead of the pinned Nat operations '
               'they ground: Nat.mul._f, Nat.mul')
    diagnostics = lines[1:]
    if diagnostics and re.fullmatch(modelled, diagnostics[0]):
        diagnostics = diagnostics[1:]
    if diagnostics and diagnostics[0] == hoisted:
        diagnostics = diagnostics[1:]
    require(lines and re.fullmatch(accepted, lines[0]) and not diagnostics,
        'Missing unambiguous verified con-ron acceptance')
    expected = {
        'source_toolchain': 'leanprover/lean4:v4.35.0-rc2',
        'kind': 'maintainer-pinned-release',
        'release_tag': 'v4.36.0-rc1',
        'release_commit': 'c9afcddf514a6772bd4d649f7cfc04eff0b9f15e',
        'archive_sha256': '26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2',
        'binary_sha256': '4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef',
        'archive_url': 'https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst',
    }
    checker = report.get('con_ron_checker', {})
    require(all(checker.get(key) == value for key, value in expected.items()) and
            report['lean_toolchain'] == expected['source_toolchain'] and
            report.get('tool_digests', {}).get('con-ron') == expected['binary_sha256'],
            'Unrecognized con-ron checker provenance or digest')



def bind_full(report, fields, files):
    require(report['status'] == 'pass' and report['stage'] == 'complete' and report['errors'] == [],
            'Full report did not complete successfully')
    source, project = fields['commit'], fields['project_path']
    require(report['source']['repository'] == fields['repository'] == REPOSITORY,
            'Report repository mismatch')
    require(report['source']['commit'] == source and report['source']['project_path'] == project,
            'Historical report is not verification of the proposed source')
    require(fields['comparator_config_path'] == project + '/comparator.json' and
            fields['formalization_metadata_path'] == project + '/formalization.yaml', 'Wrong intake paths')
    config = json.loads(files['comparator.json'])
    expected = {'formalization': 'formalization.yaml', 'comparator': 'comparator.json',
                'challenge': config['challenge_module'].replace('.', '/') + '.lean',
                'solution': config['solution_module'].replace('.', '/') + '.lean',
                'lakefile': 'lakefile.toml', 'lake_manifest': 'lake-manifest.json'}
    for kind, name in expected.items():
        require(report[kind]['path'] == project + '/' + name, kind + ' path mismatch')
        require(report[kind]['sha256'] == sha(files[name]), kind + ' source digest mismatch')
    require(report['lean_toolchain'] == files['lean-toolchain'].decode().strip(), 'Toolchain mismatch')
    protected = json.loads(report['protected_config'])
    require(sha(report['protected_config'].encode()) == report['protected_config_sha256'],
            'Protected configuration digest mismatch')
    for key in ['theorem_names', 'definition_names', 'permitted_axioms']:
        require(report['comparator'][key] == config[key] == protected[key], key + ' mismatch')
    require(protected['solution_module'] == config['solution_module'], 'Solution module mismatch')
    require(protected['challenge_module'].startswith('PalomarCanonical') and
            protected['challenge_module'].endswith('.Challenge'), 'Unprotected Challenge')
    for kind in ['challenge', 'solution']:
        require(report[kind]['module'] == config[kind + '_module'], kind + ' module mismatch')
    if project == 'algebraic-hodge/ddbar-pilot':
        # Hodge's reviewed plan follows mandatory Lean/NanoDa plus advisory con-ron.
        # Preserve main's stronger three-kernel account for every other packet;
        # when Hodge records con-ron acceptance, require its same strict provenance.
        check_kernel_account(report, protected)
        if any(k['name'] == 'con-ron' for k in report['kernels']):
            check_kernels(report, protected)
    else:
        check_kernels(report, protected)
    require(report['challenge']['trust_level'] == 'high' and report['challenge']['untrusted_sources'] == [],
            'Challenge provenance is not high trust')
    for message in ['nanoda kernel accepts the solution',
                    'Lean default kernel accepts the solution', 'Your solution is okay!']:
        require(message in report['comparator_log_tail'], 'Missing actual kernel/comparison acceptance')



def check_archive(data, files):
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:*') as archive:
        members = archive.getmembers()
        require(all(m.isfile() for m in members), 'Archive must contain only source files')
        names = [m.name.removeprefix('./') for m in members]
        require(len(names) == len(set(names)) and set(names) == set(files), 'Wrong archive source file set')
        for member, name in zip(members, names):
            require(archive.extractfile(member).read() == files[name], 'Archive source bytes differ: ' + name)


def check_status(root, commit, project, historical_report=None):
    files = snapshot(root, commit, project)
    errors = status_errors(files)
    require(not errors, '; '.join(errors))
    material_manifest = 'verification/material-imported-definitions.json'
    if project in {'topology/kuratowski-ulam', 'topology/locally-compact-baire',
                   'topology/banach-mazur-baire', 'topology/choquet-baire-product',
                   'topology/banach-mazur-category', 'topology/strong-choquet-polish',
                   'algebraic-hodge/ddbar-pilot', 'computational-hodge/finite-periods',
                   'computational-hodge/presentation-homology', 'computational-hodge/geometric-descent', 'computational-hodge/geometric-obstruction', 'computational-hodge/loop-characters'}:
        require(material_manifest in files, 'Missing material imported-definition evidence')
    if material_manifest in files:
        # Audit the proposed source bytes, never a later working directory.
        # This is static consistency; pinned-origin and compilation are separate.
        with tempfile.TemporaryDirectory(prefix='material-definition-source-') as directory:
            package = pathlib.Path(directory)
            for name, body in files.items():
                target = package / name
                require(target.resolve().is_relative_to(package.resolve()), 'Unsafe source path')
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(body)
            check_imported_definitions(package)
    if historical_report is not None:
        history = json.loads(files['verification/canonical-history.json'])
        report_bytes = pathlib.Path(historical_report).read_bytes()
        require(sha(report_bytes) in {history['full']['report_sha256'],
                    history.get('repository_preflight', {}).get('report_sha256')}, 'Unknown historical receipt digest')
        old = history['source_commit']
        old_files = snapshot(root, old, project)
        fields = dict(repository=REPOSITORY, commit=old, project_path=project,
                      comparator_config_path=project + '/comparator.json',
                      formalization_metadata_path=project + '/formalization.yaml')
        bind_full(json.loads(report_bytes), fields, old_files)
        require(sha(old_files['formalization.yaml']) == history['verified_metadata_sha256'], 'Historical metadata mismatch')
        require(sha(files['comparator.json']) == history['comparator_sha256'], 'Historical Comparator changed')
        require(files['lean-toolchain'].decode().strip() == history['lean_toolchain'] and
                sha(files['lake-manifest.json']) == history['lockfile_sha256'], 'Historical pins changed')
        meta = json.loads(files['formalization.yaml'])
        for name, text in [('README.md', files['README.md'].decode()),
                           ('formalization.yaml', meta['status']['known_gaps'])]:
            require(all(value in text for value in [old, history['comparator_sha256'], str(history['full']['run_id']),
                      str(history['rendering']['run_id'])]), name + ': missing immutable stage/source account')
        require(history['rendering']['source_commit'] == old and history['rendering']['status'] == 'pass',
                'Historical rendering source mismatch')
    return files


def check_packet(root, packet, report_bytes, report_digest, archive_bytes):
    hold = packet.get('submission_hold', {})
    require(isinstance(hold, dict) and type(hold.get('active', False)) is bool,
            'Invalid submission hold')
    require(not hold.get('active', False), 'Submission hold is active; prerequisite approval is unconfirmed')
    fields = packet.get('proposed_submission_fields', packet.get('submission_fields', packet))
    require(fields['repository'] == REPOSITORY, 'Wrong repository')
    ledger_path = pathlib.Path(root) / 'RELEASE-HANDOFFS.json'
    if ledger_path.exists():
        for row in json.loads(ledger_path.read_text())['blocked_sources']:
            require((fields['project_path'], fields['commit']) != (row['path'], row['source_commit']),
                    'Blocked or superseded source: ' + row['reason'])
    files = check_status(root, fields['commit'], fields['project_path'])
    require(sha(report_bytes) == report_digest, 'Report is not the independently recorded original bytes')
    bind_full(json.loads(report_bytes), fields, files)
    check_archive(archive_bytes, files)
    return {'status': 'pass', 'commit': fields['commit'], 'project_path': fields['project_path'],
            'metadata_sha256': sha(files['formalization.yaml']), 'report_sha256': report_digest,
            'archive_sha256': sha(archive_bytes), 'intake_authorized': False,
            'scope': 'Exact-source status, full-report and source archive consistency. Independent artifact provenance, current attempts/duplicates, rendering and editorial/registration decisions remain separate.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-path');parser.add_argument('--commit')
    parser.add_argument('--historical-report', type=pathlib.Path)
    parser.add_argument('--packet', type=pathlib.Path);parser.add_argument('--report', type=pathlib.Path)
    parser.add_argument('--report-sha256');parser.add_argument('--archive', type=pathlib.Path)
    args = parser.parse_args()
    try:
        if args.packet:
            require(all([args.report, args.report_sha256, args.archive]), 'Verified handoff requires exact-source original report/digest and source archive')
            result = check_packet(ROOT, json.loads(args.packet.read_text()), args.report.read_bytes(),
                                  args.report_sha256, args.archive.read_bytes())
        else:
            require(args.commit and args.project_path, 'Status-only mode requires exact commit and project path')
            check_status(ROOT, args.commit, args.project_path, args.historical_report)
            result = {'status': 'pass', 'mode': 'status-only', 'commit': args.commit,
                      'intake_authorized': False, 'current_source_full': 'not established by this mode'}
        print(json.dumps(result, indent=2))
    except (ValueError, KeyError, AssertionError, FileNotFoundError, subprocess.CalledProcessError) as error:
        print(json.dumps({'status': 'blocked', 'reason': str(error), 'intake_authorized': False}, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
