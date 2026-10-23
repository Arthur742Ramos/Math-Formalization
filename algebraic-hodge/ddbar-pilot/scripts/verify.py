#!/usr/bin/env python3
"""Local Lean and source checks for this pilot; not a Palomar preflight."""
import hashlib
import json
import pathlib
import re
import subprocess
import datetime

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/continuation'
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(*args):
    return subprocess.run(args, cwd=ROOT, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout


def snapshot():
    paths = sorted(p for p in ROOT.rglob('*') if p.is_file()
                   and '.lake' not in p.relative_to(ROOT).parts
                   and '__pycache__' not in p.relative_to(ROOT).parts
                   and not p.is_relative_to(OUT)
                   and p.suffix not in {'.log', '.olean', '.ilean'}
                   and p.name != 'local-report.json')
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}


def parse_audit(output, expected):
    """Accept Lean's wrapped lists while rejecting missing names or extra axioms."""
    seen = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^]]*)\]", output):
        axioms = set(filter(None, (x.strip() for x in match[2].split(','))))
        assert axioms <= ALLOWED, (match[1], axioms)
        assert match[1] not in seen, ('Duplicate audit result', match[1])
        seen[match[1]] = sorted(axioms)
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        assert match[1] not in seen, ('Duplicate audit result', match[1])
        seen[match[1]] = []
    assert expected and len(expected) == len(set(expected))
    assert set(seen) == set(expected), ('Audit names differ', set(expected) - set(seen), set(seen) - set(expected))
    return seen


def main():
    before = snapshot()
    prefix = run('git', 'rev-parse', '--show-prefix').strip()
    source_commit = run('git', 'rev-parse', 'HEAD').strip()
    for path, digest in before.items():
        committed = subprocess.check_output(['git', 'show', source_commit + ':' + prefix + path], cwd=ROOT)
        assert sha(committed) == digest, ('Source is not the recorded commit', path)
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert next(p for p in lock['packages'] if p['name'] == 'mathlib')['rev'] == PIN
    dep = (ROOT / '.lake/packages/mathlib').resolve()
    assert run('git', '-C', str(dep), 'rev-parse', 'HEAD').strip() == PIN
    assert (ROOT / 'lean-toolchain').read_bytes() == (dep / 'lean-toolchain').read_bytes()
    inventory = json.loads((ROOT / 'verification/upstream-inventory.json').read_text())
    continuation = ROOT / 'verification/continuation-inventory.json'
    if continuation.exists():
        inventory['source_files'] += json.loads(continuation.read_text())['source_files']
    for item in inventory['source_files']:
        raw = (dep / item['path']).read_bytes()
        origin = subprocess.check_output(['git', '-C', str(dep), 'show', PIN + ':' + item['path']])
        assert raw == origin and sha(raw) == item['sha256']
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == item['git_blob_sha1']
        for excerpt in item['excerpts']:
            text = b''.join(raw.splitlines(keepends=True)[excerpt['first_line']-1:excerpt['last_line']])
            assert text.decode() == excerpt['text'] and sha(text) == excerpt['sha256']
    lean_files = sorted(ROOT.glob('*.lean'))
    for p in lean_files:
        text = p.read_text()
        assert text.startswith('module\n'), p.name
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide)\b', text), p.name
    build = run('lake', 'build')
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'build.log').write_text(build)
    audit = run('lake', 'env', 'lean', '-DwarningAsError=true', 'AxiomAudit.lean')
    (OUT / 'axioms.log').write_text(audit)
    expected = re.findall(r'^#print axioms (\S+)', (ROOT / 'AxiomAudit.lean').read_text(), re.M)
    required = {
        'AlgebraicHodgePilot.Column.firstPageIso',
        'AlgebraicHodgePilot.Column.all_differentials_zero',
        'AlgebraicHodgePilot.Column.associatedSequence',
        'AlgebraicHodgePilot.Column.associatedSequence_transition',
        'AlgebraicHodgePilot.Column.bounded_e1_degeneration',
        'AlgebraicHodgePilot.Column.boundedStableGradedIso',
        'AlgebraicHodgePilot.Filtered.infinityGradedIso',
    }
    assert required <= set(expected)
    seen = parse_audit(audit, expected)
    parser_tests = run('python3', 'scripts/test_verify.py')
    (OUT / 'parser-tests.log').write_text(parser_tests)
    assert snapshot() == before, 'Source changed during verification'
    assert run('git', 'rev-parse', 'HEAD').strip() == source_commit, 'HEAD changed during verification'
    report = {
        'status': 'pass',
        'scope': 'Cloud local Lean build of actual E1 degeneration and bounded convergence, transitive axiom audit, pinned-source consistency; not Palomar verification',
        'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_commit': source_commit,
        'source_inputs_match_commit': True,
        'source_worktree_status_before_report': run('git', 'status', '--porcelain', '--', '.').splitlines(),
        'lean_version': run('lean', '--version').strip(),
        'mathlib_commit': PIN,
        'source_sha256': before,
        'local_lean_modules': [p.name for p in lean_files],
        'build_log_sha256': sha(build.encode()),
        'axiom_log_sha256': sha(audit.encode()),
        'parser_tests_log_sha256': sha(parser_tests.encode()),
        'audited_declarations': seen,
        'upstream_files_authenticated': len({f['path'] for f in inventory['source_files']}),
        'upstream_source_records_authenticated': len(inventory['source_files']),
        'all_higher_differentials_zero': True,
        'actual_quotient_pages_and_compatible_recurrence': True,
        'bounded_stabilization_and_actual_graded_cohomology_comparison': True,
        'abstract_mapping_cone_spectral_object_comparison': False,
        'protected_comparator_run': False,
        'external_kernel_checks_run': False,
        'challenge_rendered': False,
        'palomar_intake_attempted': False,
        'publication_role_check': 'arthurpalomar742 already has write; observed via connected GitHub read-only tool',
    }
    report['environment'] = {
        'host': 'selected cloud executor; no Mac commands',
        'workspace_disk_available_bytes': __import__('shutil').disk_usage(ROOT).free,
        'cgroup_memory_max_bytes': pathlib.Path('/sys/fs/cgroup/memory.max').read_text().strip(),
        'cgroup_cpu_max': pathlib.Path('/sys/fs/cgroup/cpu.max').read_text().strip(),
        'cache': 'matching pinned checkout and ignored build cache reused; missing mathlib modules fetched successfully',
        'network_limit': 'direct Palomar recent.json returned HTTP 403 during initial survey; GitHub and mathlib cache worked',
    }
    (OUT / 'local-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'pass', 'audited_declarations': len(seen),
                      'source_commit': report['source_commit'],
                      'report': 'verification/continuation/local-report.json'}))


if __name__ == '__main__':
    main()
