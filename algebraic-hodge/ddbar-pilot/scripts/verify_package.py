#!/usr/bin/env python3
"""Exact-source LOCAL package checks; does not execute protected verification."""
import argparse, datetime, hashlib, json, pathlib, subprocess, sys, tempfile
import verify
from check_interfaces import inspect

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
OUT = verify.OUT
PIPELINE_PIN = '07a02bae1e85c75ae349d0e75195162d16d41e21'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT)


def authenticated_pipeline_files(pipeline):
    """Authenticate every tracked validator/policy byte, not just checkout HEAD."""
    assert command(['git', '-C', str(pipeline), 'rev-parse', 'HEAD']).strip() == PIPELINE_PIN
    tree = subprocess.check_output(['git', '-C', str(pipeline), 'ls-tree', '-rz', PIPELINE_PIN])
    files = {}
    for row in tree.split(b'\0'):
        if not row:
            continue
        fields, path = row.split(b'\t', 1)
        mode, kind, blob = fields.split()
        assert kind == b'blob' and mode in {b'100644', b'100755'}
        relative = path.decode()
        file = pipeline / relative
        assert not file.is_symlink()
        raw = file.read_bytes()
        observed = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert observed == blob.decode(), ('Pipeline worktree differs from pin', relative)
        files[relative] = sha(raw)
    assert not command(['git', '-C', str(pipeline), 'ls-files', '--others', '--exclude-standard']).strip(), 'Untracked pipeline files'
    return files


def main(pipeline):
    assert not (OUT / 'local-report.json').exists(), 'Refusing to overwrite an existing immutable local receipt; choose a fresh HODGE_EVIDENCE_DIR'
    head = command(['git', 'rev-parse', 'HEAD']).strip()
    tools = {}
    for path in ['scripts/check_imported_definitions.py', 'tests/test_imported_definitions.py']:
        raw = (REPO / path).read_bytes()
        assert raw == subprocess.check_output(['git', 'show', head + ':' + path], cwd=REPO)
        tools[path] = sha(raw)
    pipeline_files = authenticated_pipeline_files(pipeline)
    sys.path.insert(0, str(pipeline))
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import load_comparator_config
    from scripts.source_requirements import inspect_lean_sources
    metadata = load_formalization_metadata(ROOT / 'formalization.yaml')
    config = load_comparator_config(ROOT / 'comparator.json')
    roles = ['Arthur Freitas Ramos', 'Ruy Jose Guerra Barretto de Queiroz', 'David Barros Hulak']
    assert metadata['project']['authors'] == roles == metadata['project']['responsible_maintainers']
    assert all(person in ' '.join((ROOT / 'README.md').read_text().split()) for person in roles)
    constraints, issues = inspect_lean_sources(REPO)
    assert not issues, [str(issue) for issue in issues]
    verify.main()
    report = json.loads((OUT / 'local-report.json').read_text())
    report.update(status='incomplete', stage='remaining-local-package-checks')
    (OUT / 'local-report.json').write_text(json.dumps(report, indent=2) + '\n')
    initial = dict(report['source_sha256'])
    regeneration = command(['python3', 'scripts/make_challenge.py', '--check'])
    (OUT / 'challenge-regeneration.log').write_text(regeneration)
    inventory = []
    for suffix, args in [('static', []), ('exact-pin', ['--dependency-root', str(ROOT / '.lake/packages/mathlib')])]:
        raw = command(['python3', str(REPO / 'scripts/check_imported_definitions.py'), '--project-path', str(ROOT), *args])
        (OUT / ('inventory-' + suffix + '.json')).write_text(raw)
        inventory.append(json.loads(raw))
    tests = command(['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_imported_definitions.py'], REPO)
    (OUT / 'inventory-validator-tests.log').write_text(tests)
    audit = command(['lake', 'env', 'lean', '-DwarningAsError=true', 'HodgeChallengeAudit.lean'])
    (OUT / 'challenge-axioms.log').write_text(audit)
    selected = config['theorem_names'] + config['definition_names']
    selected_axioms = verify.parse_audit(audit, selected)
    with tempfile.TemporaryDirectory(prefix='hodge-solution-audit-') as tmp:
        probe = pathlib.Path(tmp) / 'SolutionAudit.lean'
        probe.write_text((ROOT / 'HodgeChallengeAudit.lean').read_text().replace('import Challenge', 'import HodgeSolution'))
        solution_audit = command(['lake', 'env', 'lean', '-DwarningAsError=true', str(probe)])
    (OUT / 'solution-axioms.log').write_text(solution_audit)
    solution_axioms = verify.parse_audit(solution_audit, selected)
    interface = inspect()
    (OUT / 'interfaces-and-source-closure.json').write_text(json.dumps(interface, indent=2) + '\n')
    assert verify.snapshot() == initial and command(['git', 'rev-parse', 'HEAD']).strip() == head
    assert report['source_commit'] == head
    assert authenticated_pipeline_files(pipeline) == pipeline_files
    report.update({
        'status': 'pass',
        'stage': 'local-package-complete',
        'scope': 'Exact-source LOCAL Challenge/Solution package build, selected and modular axiom audits, metadata/config validation, material-definition consistency and pinned source closure. No protected Comparator or external kernel replay.',
        'repository_tool_sha256': tools,
        'canonical_pipeline_validation_commit': PIPELINE_PIN,
        'canonical_pipeline_worktree_file_sha256': pipeline_files,
        'metadata_schema_and_comparator_configuration_valid': True,
        'source_requirements': constraints,
        'selected_theorem_count': len(config['theorem_names']),
        'selected_definition_count': len(config['definition_names']),
        'selected_challenge_axioms': selected_axioms,
        'selected_solution_axioms': solution_axioms,
        'material_inventory': inventory[-1],
        'compiled_challenge_module_count': len(interface['source_modules']),
        'local_interface_types_kernel_defeq_in_solution_environment': True,
        'local_exact_pinned_compareAt_and_literal_definition_values': True,
        'local_interface_limit': 'Actual pinned comparison function over writable local environments, including random Challenge alias and in-memory rejection controls; no protected canonical run or external-kernel replay.',
        'challenge_bytes': (ROOT / 'Challenge.lean').stat().st_size,
        'challenge_lines': len((ROOT / 'Challenge.lean').read_text().splitlines()),
        'challenge_readability_warning': True,
        'protected_comparator_run': False,
        'protected_positive_negative_controls_run': False,
        'external_kernel_checks_run': False,
        'challenge_rendered': False,
        'browser_visual_inspection_run': False,
        'release_packet_guard_run': False,
        'canonical_execution_blocker': 'Corrected source has not had a canonical run. Original source c3107f8 failed in approved run39894330468; that approval is consumed. No new hosted run is authorized. Local namespace restrictions remain; no security workaround attempted.',
        'completed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    })
    (OUT / 'local-report.json').write_text(json.dumps(report, indent=2) + '\n')
    artifacts = {f.name: sha(f.read_bytes()) for f in sorted(OUT.iterdir()) if f.is_file() and f.name not in {'artifact-hashes.json', 'review-receipt.json', 'final-evidence-review.json', 'source-binding.json'}}
    (OUT / 'artifact-hashes.json').write_text(json.dumps(artifacts, indent=2) + '\n')
    print(json.dumps({'status': 'pass', 'source_commit': head, 'selected_declarations': len(selected), 'modular_audits': len(report['audited_declarations']), 'source_modules': len(interface['source_modules']), 'report': str(OUT / 'local-report.json')}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pipeline-root', type=pathlib.Path, required=True)
    main(parser.parse_args().pipeline_root.resolve())
