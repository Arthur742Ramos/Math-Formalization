"""Validate frozen preparations separately from the canonical-pass readiness ledger."""
import hashlib
import json
import pathlib
import re
import subprocess

from check_readiness import check_full_report
from check_release_packet import bind_full, snapshot

ROOT = pathlib.Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def check_status_correction(p, source, tree):
    """Preserve the historical source while allowing only the reviewed status repair."""
    change = p['status_correction']
    assert change['kind'] == 'verification-status-account'
    assert p['state'] in {'status-correction-awaiting-exact-source-verification',
                          'status-correction-full-verified'}
    assert change['historical_source'] == source
    corrected = p['current_source_snapshot']
    assert change['corrected_source'] == corrected['commit']
    assert change['corrected_tree'] == corrected['tree']
    assert git('rev-parse', source + ':' + p['path']) == tree
    assert git('rev-parse', corrected['commit'] + ':' + p['path']) == corrected['tree']
    assert git('rev-parse', 'HEAD:' + p['path']) == corrected['tree']
    allowed = {'README.md', 'REVIEW.md', 'VERIFICATION.md', 'formalization.yaml',
               'scripts/check_package.py', 'verification/canonical-history.json',
               'verification/source-hashes.json'}
    assert set(change['allowed_changed_files']) == allowed
    actual = set(git('diff', '--name-only', source, 'HEAD', '--', p['path']).splitlines())
    assert actual == {p['path'] + '/' + name for name in allowed}
    for name in allowed:
        assert git('rev-parse', 'HEAD:' + p['path'] + '/' + name) == git('rev-parse', corrected['commit'] + ':' + p['path'] + '/' + name)
    before = json.loads(git('show', source + ':' + p['path'] + '/formalization.yaml'))
    after = json.loads((ROOT / p['path'] / 'formalization.yaml').read_text())
    before['status']['known_gaps'] = after['status']['known_gaps']
    assert before == after, 'Only metadata known_gaps may change'
    assert p['current_source_rendering'] == 'not-established'
    if p['current_source_full'] == 'pass':
        assert p['state'] == 'status-correction-full-verified'
        full = p['current_source_full_run']
        assert full['repository'] == 'Arthur742Ramos/Math-Formalization'
        assert full['attempt'] == 1
        report = ROOT / full['report_file']
        assert report.resolve().is_relative_to((ROOT / 'catalog-evidence').resolve())
        assert hashlib.sha256(report.read_bytes()).hexdigest() == full['report_sha256']
        assert full['source_commit'] == corrected['commit']
        assert full['url'] == f'https://github.com/{full["repository"]}/actions/runs/{full["run_id"]}'
        original = json.loads(report.read_bytes())
        assert original['workflow_url'] == full['url']
        bind_full(original, dict(repository='Arthur742Ramos/Math-Formalization',
            commit=corrected['commit'], project_path=p['path'],
            comparator_config_path=p['path'] + '/comparator.json',
            formalization_metadata_path=p['path'] + '/formalization.yaml'),
            snapshot(ROOT, corrected['commit'], p['path']))
    else:
        assert p['current_source_full'] == 'not-established'
        assert p['state'] == 'status-correction-awaiting-exact-source-verification'


def check_verified(p, package, source, tree):
    """Require completed source-bound canonical and rendered evidence for this preparation."""
    evidence = ROOT / {
        'topology/collectionwise-normal': 'catalog-evidence/collectionwise-2026-10-18',
        'topology/sigma-product-compactness': 'catalog-evidence/sigma-compact-2026-10-18',
        'topology/product-countable-chain-condition': 'catalog-evidence/product-ccc-2026-10-19',
        'topology/kuratowski-ulam': 'catalog-evidence/kuratowski-ulam-2026-10-19',
        'topology/locally-compact-baire': 'catalog-evidence/locally-compact-baire-2026-10-19',
    }[p['path']]
    ledger = json.loads((ROOT / 'READINESS.json').read_text())
    corrected = 'status_correction' in p
    assert p['canonical_full'] == p['rendering'] == ('historical-pass' if corrected else 'pass')
    reported = p['state'] == 'user-reported-submitted'
    unconfirmed = p['state'] == 'verified-preparation-intake-unconfirmed'
    assert p['fresh_runner_security_approval'] is (not (corrected or reported or unconfirmed))
    if unconfirmed:
        check_unconfirmed_intake(p)
    if reported:
        assert not corrected
        check_user_submission_report(p)
    assert p['source_snapshot']['commit'] == source
    canonical = p['canonical_run']
    rendered = p['rendering_run']
    for run in [canonical, rendered]:
        assert run['status'] == 'completed' and run['conclusion'] == 'success'
        assert run['attempt'] == 1
        assert run['tested_package_tree'] == tree and run['current_package_tree_equal'] is (not corrected)
        assert run['verified_source_commit'] == source
        assert run['url'] == f'https://github.com/{ledger["repository"]}/actions/runs/{run["run_id"]}'
        assert git('rev-parse', run['workflow_head'] + ':' + p['path']) == tree
    bound = {
        'comparator_sha256': p['source_files_sha256']['comparator.json'],
        'metadata_sha256': p['source_files_sha256']['formalization.yaml'],
        'lockfile_sha256': p['source_files_sha256']['lake-manifest.json'],
        'toolchain': (package / 'lean-toolchain').read_text().strip(),
    }
    check_full_report(canonical, ledger, p['path'], bound, tree, evidence)
    report_file = ROOT / rendered['report_file']
    assert report_file.resolve().is_relative_to(evidence.resolve())
    assert hashlib.sha256(report_file.read_bytes()).hexdigest() == rendered['original_report_sha256']
    report = json.loads(report_file.read_text())
    assert report['status'] == 'pass' and report['stage'] == 'complete' and report['errors'] == []
    assert report['source']['repository'] == ledger['repository']
    assert report['source']['commit'] == source and report['source']['project_path'] == p['path']
    config = json.loads((package / 'comparator.json').read_text())
    assert report['surface']['declarations'] == config['theorem_names'] + config['definition_names']
    assert [d['name'] for d in report['surface']['audit_declarations']] == config['theorem_names'] + config['definition_names']
    challenge = p['path'] + '/' + config['challenge_module'].replace('.', '/') + '.lean'
    assert report['source']['challenge_path'] == challenge
    assert report['source']['challenge_sha256'] == hashlib.sha256((ROOT / challenge).read_bytes()).hexdigest()
    assert report['source']['solution_path'] == p['path'] + '/' + config['solution_module'].replace('.', '/') + '.lean'
    assert report['source']['comparator_config_path'] == p['path'] + '/comparator.json'
    assert report['lean_toolchain'] == bound['toolchain']
    assert report['workflow_url'] == rendered['url']
    assert report['renderer_commit'] == ledger['completion']['pipeline_commit']
    assert re.fullmatch(r'[0-9a-f]{64}', report['artifact_tree_sha256'])
    assert report['artifact_tree_sha256'] == rendered['artifact_tree_sha256']
    assert report['source']['lakefile_path'] == p['path'] + '/lakefile.toml'
    assert report['source']['lean_toolchain_path'] == p['path'] + '/lean-toolchain'
    assert report['entrypoint'] == 'Challenge/index.html'
    caller = git('show', rendered['workflow_head'] + ':' + rendered['workflow'])
    assert '--commit ' + source in caller and 'ref: ' + source in caller
    assert 'PALOMAR_EXECUTION_PROFILE: palomar-standard-v1' in caller
    assert 'ref: ' + report['renderer_commit'] in caller
    assert '--renderer-commit ' + report['renderer_commit'] in caller


def check_user_submission_report(p):
    """User-reported intake is not editorial acceptance or public registration."""
    report = p['latest_user_report']
    assert report['classification'] == 'user-reported-submitted'
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z', report['observed_at_utc'])
    assert report['actor'] == 'user'
    assert report['acceptance'] == report['registration'] == 'unverified'
    assert report['public_registration_id'] is None
    assert p['existing_public_id'] is None
    assert p['registry_intakes_by_this_task'] == 0
    assert p['registry_submission_ready'] is False
    assert p['fresh_runner_security_approval'] is False


def check_unconfirmed_intake(p):
    """Completed mechanical evidence cannot establish a private intake or registration."""
    assert p['state'] == 'verified-preparation-intake-unconfirmed'
    assert p['registry_intake_status'] == p['registry_registration_status'] == 'unconfirmed'
    assert p['existing_public_id'] is None
    assert p['registry_intakes_by_this_task'] == 0
    assert p['registry_submission_ready'] is False
    assert p['fresh_runner_security_approval'] is False


def check_material_definition_correction(p, source, tree):
    """Retain the old mechanical pass without transferring it to edited evidence."""
    change = p['definition_evidence_correction']
    assert change['kind'] == 'material-imported-definition-evidence'
    old = change['prior_verified_snapshot']
    old_source = old['commit']
    assert old_source != source
    assert git('rev-parse', old_source + ':' + p['path']) == old['tree']
    assert git('rev-parse', source + ':' + p['path']) == tree
    allowed = {'ChallengeTests.lean', 'SemanticTests.lean', 'README.md', 'REVIEW.md',
        'VERIFICATION.md', 'formalization.yaml', 'scripts/check_package.py',
        'verification/source-hashes.json', 'MATERIAL-DEFINITIONS.md',
        'verification/material-imported-definitions.json'}
    assert set(change['allowed_changed_files']) == allowed
    actual = set(git('diff', '--name-only', old_source, source, '--', p['path']).splitlines())
    assert actual == {p['path'] + '/' + name for name in allowed}
    old_files = snapshot(ROOT, old_source, p['path'])
    new_files = snapshot(ROOT, source, p['path'])
    for name in set(old_files) - allowed:
        assert old_files[name] == new_files[name], ('Preserved proof/pin source changed', name)
    before = json.loads(old_files['formalization.yaml'])
    after = json.loads(new_files['formalization.yaml'])
    before['related_formalizations'][0]['note'] = after['related_formalizations'][0]['note']
    assert before == after, 'Only metadata imported-definition explanation may change'
    for kind in ['full', 'rendering']:
        historical = old[kind]
        assert historical['status'] == 'pass' and historical['attempt'] == 1
        assert type(historical['run_id']) is int and historical['run_id'] > 0
        assert historical['url'] == f'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/{historical["run_id"]}'
        report_path = (ROOT / historical['report_file']).resolve()
        assert report_path.is_relative_to((ROOT / 'catalog-evidence').resolve())
        body = report_path.read_bytes()
        assert hashlib.sha256(body).hexdigest() == historical['report_sha256']
        report = json.loads(body)
        assert report['source']['commit'] == old_source
        assert report['source']['repository'] == 'Arthur742Ramos/Math-Formalization'
        assert report['source']['project_path'] == p['path']
        assert report['status'] == 'pass' and report['stage'] == 'complete' and report['errors'] == []
        assert report['workflow_url'] == historical['url']
        if kind == 'full':
            bind_full(report, dict(repository='Arthur742Ramos/Math-Formalization',
                commit=old_source, project_path=p['path'],
                comparator_config_path=p['path'] + '/comparator.json',
                formalization_metadata_path=p['path'] + '/formalization.yaml'), old_files)
        else:
            config = json.loads(old_files['comparator.json'])
            assert report['surface']['declarations'] == config['theorem_names'] + config['definition_names']
            assert report['source']['challenge_sha256'] == hashlib.sha256(old_files['KUChallenge.lean']).hexdigest()
    assert p['state'] == 'reviewed-preparation-not-submitted'
    assert p['canonical_full'] == p['rendering'] == 'not-established'
    assert p['canonical_run'] is None and p['rendering_run'] is None
    assert p['fresh_runner_security_approval'] is False


def check_locally_compact_definition_preparation(p, source, tree):
    """Bind prior ordinary evidence without promoting it to new-source canonical evidence."""
    assert p['path'] == 'topology/locally-compact-baire'
    history = p['prior_ordinary_source']
    old = history['source_commit']
    assert old == '56c93c5ab4cdc1291d87c0b17104cb31f7c243dc' and source != old
    assert history['package_tree'] == git('rev-parse', old + ':' + p['path'])
    head = history['reviewed_head']
    assert git('rev-parse', head + ':' + p['path']) == history['package_tree']
    record = ROOT / history['provider_record']
    assert record.resolve().is_relative_to((ROOT / 'catalog-evidence').resolve())
    assert hashlib.sha256(record.read_bytes()).hexdigest() == history['provider_record_sha256']
    provider = json.loads(record.read_text())
    for kind in ['lean', 'catalog']:
        run = provider[kind]
        assert history[kind + '_run'] == run['id']
        assert run['head_sha'] == head and run['head_branch'] == 'topology/locally-compact-baire'
        assert run['run_attempt'] == history['attempts'] == 1
        assert run['status'] == 'completed' and run['conclusion'] == history['conclusion'] == 'success'
        assert run['html_url'] == f'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/{run["id"]}'
    assert history['lean_run'] == 39265820552 and history['catalog_run'] == 39265820469
    changed = {'ChallengeTests.lean', 'SemanticTests.lean', 'MATERIAL-DEFINITIONS.md',
        'README.md', 'REVIEW.md', 'VERIFICATION.md', 'formalization.yaml', 'scripts/check_package.py',
        'verification/material-imported-definitions.json', 'verification/source-hashes.json'}
    assert set(git('diff', '--name-only', old, source, '--', p['path']).splitlines()) == {
        p['path'] + '/' + n for n in changed}
    before, after = snapshot(ROOT, old, p['path']), snapshot(ROOT, source, p['path'])
    assert all(before[n] == after[n] for n in before if n not in changed)
    audit = p['material_definition_audit']
    assert audit['source_commit'] == source
    assert git('rev-parse', source + ':' + p['path']) == tree
    assert audit['manifest'] == 'verification/material-imported-definitions.json'
    manifest = json.loads(after[audit['manifest']])
    assert audit['schema_version'] == manifest['schema_version'] == 2
    assert audit['material_declarations'] == len(manifest['material_declarations']) == 10
    assert audit['upstream_files'] == len(manifest['source_files']) == 15
    assert audit['literal_excerpts'] == sum(len(f['excerpts']) for f in manifest['source_files']) == 35
    assert audit['semantic_tests'] == ['ChallengeTests.lean', 'SemanticTests.lean']
    if p['state'] == 'reviewed-preparation-not-submitted':
        assert p['canonical_full'] == p['rendering'] == 'not-established'
        assert p['canonical_run'] is None and p['rendering_run'] is None
    else:
        assert p['state'] == 'verified-preparation-intake-unconfirmed'
        check_verified(p, ROOT / p['path'], source, tree)
    assert p['fresh_runner_security_approval'] is False


def check_material_audit_binding(p, source):
    """Bind a preparation's summary to its exact retained source evidence."""
    assert 'material_definition_audit' in p, 'Missing required retained audit'
    audit = p['material_definition_audit']
    assert audit['source_commit'] == source
    assert audit['manifest'] == 'verification/material-imported-definitions.json'
    manifest = json.loads(git('show', source + ':' + p['path'] + '/' + audit['manifest']))
    assert audit['schema_version'] == manifest['schema_version']
    assert audit['material_declarations'] == len(manifest['material_declarations'])
    assert audit['upstream_files'] == len(manifest['source_files'])
    assert audit['literal_excerpts'] == sum(len(f['excerpts']) for f in manifest['source_files'])
    assert audit['semantic_tests'] == [b['path'] for b in manifest['checked_bridge_modules']]
    if p['path'] == 'topology/banach-mazur-baire':
        proof = git('show', source + ':' + p['path'] + '/BanachMazur.lean')
        fixed = ['BanachMazur.' + n for n in re.findall(r'^@\[expose\] def (\w+)', proof, re.M)]
        assert len(fixed) == 4 and p['fixed_model_definitions'] == fixed
        assert p['definition_names'] == [], 'Fixed game meanings must not become holes'


def check_preparations(rows, verified_paths):
    data = json.loads((ROOT / 'PREPARATIONS.json').read_text())
    assert data['schema_version'] == 1
    assert data['repository'] == 'Arthur742Ramos/Math-Formalization'
    seen = set()
    for p in data['projects']:
        path = p['path']
        assert re.fullmatch(r'topology/[a-z0-9-]+', path)
        assert path not in seen | verified_paths
        seen.add(path)
        assert p['state'] in {'reviewed-preparation-not-submitted', 'verified-preparation-not-submitted',
            'status-correction-awaiting-exact-source-verification', 'status-correction-full-verified',
            'user-reported-submitted', 'verified-preparation-intake-unconfirmed'}
        source, tree = p['source_snapshot']['commit'], p['source_snapshot']['tree']
        assert re.fullmatch(r'[0-9a-f]{40}', source) and re.fullmatch(r'[0-9a-f]{40}', tree)
        assert git('rev-parse', source + ':' + path) == tree
        if path == 'topology/banach-mazur-baire' or 'material_definition_audit' in p:
            check_material_audit_binding(p, source)
        if 'definition_evidence_correction' in p:
            check_material_definition_correction(p, source, tree)
        if path == 'topology/locally-compact-baire':
            check_locally_compact_definition_preparation(p, source, tree)
        if 'status_correction' in p:
            check_status_correction(p, source, tree)
        else:
            assert git('rev-parse', 'HEAD:' + path) == tree
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', source, 'HEAD'], check=True)
        package = ROOT / path
        for name, expected in p['source_files_sha256'].items():
            assert pathlib.Path(name).name == name
            assert hashlib.sha256(subprocess.check_output(['git', '-C', str(ROOT), 'show', source + ':' + path + '/' + name])).hexdigest() == expected
        config = json.loads((package / 'comparator.json').read_text())
        meta = json.loads((package / 'formalization.yaml').read_text())
        assert p['theorem_names'] == config['theorem_names']
        assert p['definition_names'] == config['definition_names']
        assert p['authors'] == meta['project']['authors']
        assert p['responsible_maintainers'] == meta['project']['responsible_maintainers']
        if p['state'] == 'reviewed-preparation-not-submitted':
            # Evidence at this dated preparation checkpoint, not a permanent
            # claim that later exact-source external checks have never run.
            assert p['canonical_full'] == p['rendering'] == 'not-established'
            assert p['canonical_run'] is None and p['rendering_run'] is None
            assert p['fresh_runner_security_approval'] is False
        else:
            check_verified(p, package, source, tree)
        assert p['registry_submission_ready'] is False and p['registry_intakes_by_this_task'] == 0
        assert p['existing_public_id'] is None
        assert p['reviews']['kind'] == 'independent-internal-AI'
        assert p['reviews']['mathematical_source'] == p['reviews']['implementation'] == 'pass'
        for digest in p['reviews']['receipts_sha256'].values():
            assert re.fullmatch(r'[0-9a-f]{64}', digest)
        matching = [row for row in rows if '](' + path + ')' in row]
        assert len(matching) == 1
        label = ('Source-account correction' if 'status_correction' in p else
                 'User-reported submitted' if p['state'] == 'user-reported-submitted' else
                 'Full/render passed; intake and registration unconfirmed' if p['state'] == 'verified-preparation-intake-unconfirmed' else
                 'Preparation; not submitted')
        assert label in matching[0]
        assert p['name'] in matching[0]
        catalog_source = p.get('current_source_snapshot', p['source_snapshot'])['commit']
        assert f'https://github.com/{data["repository"]}/tree/{catalog_source}/{path}' in matching[0]
        result = subprocess.run(['python3', 'scripts/check_package.py'], cwd=package,
                                capture_output=True, text=True)
        assert result.returncode == 0, (path, result.stdout, result.stderr)
    return seen
