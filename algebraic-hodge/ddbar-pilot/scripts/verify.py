#!/usr/bin/env python3
"""Local Lean and source checks for this pilot; not a Palomar preflight."""
import hashlib
import json
import pathlib
import re
import subprocess
import datetime

ROOT = pathlib.Path(__file__).resolve().parents[1]
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
                   and p.suffix not in {'.log', '.olean', '.ilean'}
                   and p.name != 'local-report.json')
    return {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}


def main():
    before = snapshot()
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert next(p for p in lock['packages'] if p['name'] == 'mathlib')['rev'] == PIN
    dep = (ROOT / '.lake/packages/mathlib').resolve()
    assert run('git', '-C', str(dep), 'rev-parse', 'HEAD').strip() == PIN
    assert (ROOT / 'lean-toolchain').read_bytes() == (dep / 'lean-toolchain').read_bytes()
    inventory = json.loads((ROOT / 'verification/upstream-inventory.json').read_text())
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
    (ROOT / 'verification/build.log').write_text(build)
    audit = run('lake', 'env', 'lean', '-DwarningAsError=true', 'AxiomAudit.lean')
    (ROOT / 'verification/axioms.log').write_text(audit)
    expected = re.findall(r'^#print axioms (\S+)', (ROOT / 'AxiomAudit.lean').read_text(), re.M)
    seen = {}
    for line in audit.splitlines():
        m = re.match(r"'([^']+)' depends on axioms: \[([^]]*)\]", line)
        n = re.match(r"'([^']+)' does not depend on any axioms", line)
        if m:
            axioms = set(filter(None, (x.strip() for x in m[2].split(','))))
            assert axioms <= ALLOWED, (m[1], axioms)
            seen[m[1]] = sorted(axioms)
        elif n:
            seen[n[1]] = []
    assert set(seen) == set(expected) and len(seen) == 20
    assert snapshot() == before, 'Source changed during verification'
    report = {
        'status': 'pass',
        'scope': 'Cloud local Lean build, transitive axiom audit, pinned-source consistency; not full degeneration or Palomar verification',
        'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_commit': run('git', 'rev-parse', 'HEAD').strip(),
        'source_worktree_status_before_report': run('git', 'status', '--porcelain', '--', '.').splitlines(),
        'lean_version': run('lean', '--version').strip(),
        'mathlib_commit': PIN,
        'source_sha256': before,
        'build_log_sha256': sha(build.encode()),
        'axiom_log_sha256': sha(audit.encode()),
        'audited_declarations': seen,
        'upstream_files_authenticated': len(inventory['source_files']),
        'full_e1_degeneration_proved': False,
        'associated_filtered_spectral_sequence_constructed': False,
        'protected_comparator_run': False,
        'external_kernel_checks_run': False,
        'challenge_rendered': False,
        'palomar_intake_attempted': False,
        'publication_role_check': 'arthurpalomar742 already has write; observed via connected GitHub read-only tool',
    }
    (ROOT / 'verification/local-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'pass', 'audited_declarations': len(seen),
                      'source_commit': report['source_commit'],
                      'report': 'verification/local-report.json'}))


if __name__ == '__main__':
    main()
