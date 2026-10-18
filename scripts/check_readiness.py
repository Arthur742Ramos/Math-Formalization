"""Validate saved source-bound readiness evidence without builds or network."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'catalog-evidence/readiness-2026-10-18'


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def check_axiom_log(text, selected, allowed):
    """Require every selected theorem AND definition, with permitted closure."""
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    names = [name for name, _ in reports]
    assert len(names) == len(set(names)), 'duplicate axiom reports'
    assert set(names) == set(selected), ('selected axiom coverage', set(selected) - set(names))
    result = {}
    for name, raw in reports:
        axioms = [item.strip() for item in raw.split(',') if item.strip()]
        assert set(axioms) <= set(allowed), (name, 'unapproved axiom', axioms)
        result[name] = axioms
    return result


def check():
    ledger = read(ROOT / 'READINESS.json')
    catalog = read(ROOT / 'REGISTRATIONS.json')
    assert ledger['schema_version'] == 1
    assert ledger['repository'] == catalog['repository']
    assert ledger['baseline_commit'] == catalog['readiness_audit']['baseline_commit']
    assert git('rev-parse', ledger['baseline_commit'] + '^{tree}') == ledger['baseline_root_tree']
    subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor',
                    ledger['baseline_commit'], 'HEAD'], check=True)
    projects = {p['path']: p for p in ledger['projects']}
    records = {p['path']: p for p in catalog['projects']}
    assert len(projects) == len(ledger['projects']) == len(records) == 17
    assert set(projects) == set(records)
    official = read(EVIDENCE / 'official-registration-summaries.json')
    entries = {e['source']['project_path']: e for e in official['entries']}
    assert len(entries) == len(official['entries']) == 10
    assert official['revision'] == ledger['registry_snapshot']['revision'] == catalog['registry_revision']
    assert official['release'] == ledger['registry_snapshot']['release'] == catalog['registry_release']
    assert official['captured_at'] == ledger['registry_snapshot']['capture_checked_at']
    manifest = read(EVIDENCE / 'manifest.json')['files']
    assert set(manifest) == {p.name for p in EVIDENCE.iterdir() if p.is_file() and p.name != 'manifest.json'}
    for name, expected in manifest.items():
        assert pathlib.Path(name).name == name
        assert sha(EVIDENCE / name) == expected, (name, 'evidence hash')
    totals = dict(projects=len(projects), selected_theorems=0, selected_definitions=0,
                  full_success_equal_package_trees=0, named_renderer_success=0,
                  registered_preview_only=0, rendering_not_established=0,
                  official_registrations_evidenced=0, user_reported_ids_unconfirmed=0,
                  other_registration_outcomes_unknown=0)
    for path, p in projects.items():
        package = ROOT / path
        config = read(package / 'comparator.json')
        assert p['catalog_source_commit'] == records[path]['source_snapshot']['commit']
        tree = p['package_tree']
        for commit in ['HEAD', ledger['baseline_commit'], p['catalog_source_commit']]:
            assert git('rev-parse', commit + ':' + path) == tree, (path, commit, 'tree')
        for key, filename in [('comparator_sha256', 'comparator.json'),
                              ('metadata_sha256', 'formalization.yaml'),
                              ('lockfile_sha256', 'lake-manifest.json')]:
            assert sha(package / filename) == p[key], (path, filename)
        assert (package / 'lean-toolchain').read_text().strip() == p['toolchain']
        lock = read(package / 'lake-manifest.json')
        assert next(x['rev'] for x in lock['packages'] if x['name'] == 'mathlib') == p['mathlib_commit']
        for key in ['theorem_names', 'definition_names']:
            assert p[key] == config.get(key, [])
        assert p['permitted_axioms'] == config['permitted_axioms']
        totals['selected_theorems'] += len(p['theorem_names'])
        totals['selected_definitions'] += len(p['definition_names'])
        # A successful workflow head may differ from its pinned source: bind its
        # package tree explicitly rather than asserting those commits are equal.
        for key in ['full_verification', 'ordinary_verification', 'rendering']:
            run = p[key]
            if run is None:
                assert key != 'full_verification'
                continue
            assert run['status'] == 'completed' and run['conclusion'] == 'success'
            assert run['url'] == f'https://github.com/{ledger["repository"]}/actions/runs/{run["run_id"]}'
            assert run['tested_package_tree'] == tree and run['current_package_tree_equal'] is True
            assert git('rev-parse', run['workflow_head'] + ':' + path) == tree, (path, key)
        totals['full_success_equal_package_trees'] += 1
        if p['rendering']:
            assert p['rendering_evidence'] == 'named-monorepo-renderer-success'
            totals['named_renderer_success'] += 1
        elif path in entries:
            assert p['rendering_evidence'] == 'registered-preview-summary'
            assert re.fullmatch('[0-9a-f]{64}', entries[path]['preview']['artifact_tree_sha256'])
            totals['registered_preview_only'] += 1
        else:
            assert p['rendering_evidence'] == 'not-established'
            totals['rendering_not_established'] += 1
        if path in entries:
            entry = entries[path]
            registration = p['registration']
            assert p['registration_state'] == 'official-registration-evidenced'
            assert entry['status'] == 'registered' and entry['source']['commit'] == p['catalog_source_commit']
            assert entry['source']['repository'] == ledger['repository']
            assert registration['id'] == entry['id'] == records[path]['registration']['id']
            assert registration['version'] == entry['version'] == records[path]['registration']['version']
            assert registration['source_commit'] == entry['source']['commit']
            assert registration['preview'] == entry['preview']
            assert entry['formalization']['theorem_names'] == p['theorem_names']
            totals['official_registrations_evidenced'] += 1
        else:
            assert p['registration'] is None
            if p['user_reported_at_utc']:
                assert p['registration_state'] == 'user-reported-registration-id-unconfirmed'
                assert records[path]['status'] == 'registration-pending'
                totals['user_reported_ids_unconfirmed'] += 1
            else:
                assert p['registration_state'] == 'editorial-and-intake-outcome-not-evidenced'
                totals['other_registration_outcomes_unknown'] += 1
    assert ledger['totals'] == totals
    supplemental_count = 0
    for audit in read(EVIDENCE / 'supplemental-selected-axiom-audits.json'):
        p = projects[audit['path']]
        selected = p['theorem_names'] + p['definition_names']
        assert audit['selected_names'] == selected
        assert audit['package_tree'] == p['package_tree']
        assert audit['original_lockfile_sha256'] == p['lockfile_sha256']
        assert audit['source_commit'] == ledger['baseline_commit']
        assert audit['status'] == 'pass' and audit['all9_dependency_checkout_pins_match']
        log = EVIDENCE / audit['axiom_log']
        query = EVIDENCE / audit['query_input']
        assert sha(log) == audit['axiom_log_sha256']
        assert sha(query) == audit['supplemental_input_sha256']
        assert re.findall(r'^#print axioms (\S+)$', query.read_text(), re.M) == selected
        closures = check_axiom_log(log.read_text(), selected, p['permitted_axioms'])
        assert closures == audit['axiom_closures']
        supplemental_count += len(closures)
    sorgenfrey = projects['topology/sorgenfrey-covering']
    host = read(EVIDENCE / 'sorgenfrey-hosted-axiom-binding.json')
    assert git('rev-parse', host['workflow_commit'] + ':' + sorgenfrey['path']) == sorgenfrey['package_tree']
    assert host['axiom_gate_step_conclusion'] == 'success'
    assert set(sorgenfrey['theorem_names'] + sorgenfrey['definition_names']) <= set(host['axiom_reports'])
    check_axiom_log((EVIDENCE / 'sorgenfrey-selected-axioms.log').read_text(),
                    list(host['axiom_reports']), sorgenfrey['permitted_axioms'])
    branches = ledger['branches_at_baseline']
    assert len(branches) == 20 and len({b['name'] for b in branches}) == 20
    assert sum(not b['fully_merged_by_ancestry'] for b in branches) == 1
    for branch in branches:
        merged = subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor',
                                  branch['tip'], ledger['baseline_commit']]).returncode == 0
        assert merged == branch['fully_merged_by_ancestry']
    prs = ledger['pull_requests_at_baseline']
    assert len(prs) == 19 and all(p['state'] == 'closed' and p['merged_at'] for p in prs)
    # Do not require the unpublished candidate object in CI's remote checkout.
    candidate = ledger['sorgenfrey_candidate']
    assert candidate['published'] is False
    assert candidate['original_user_commit'] == next(b['tip'] for b in branches if not b['fully_merged_by_ancestry'])
    print(json.dumps({'status': 'pass', 'scope': 'Saved evidence and source bindings; no new Lean/Comparator execution or registry certification',
                      **totals, 'supplemental_selected_axiom_reports': supplemental_count,
                      'sorgenfrey_hosted_axiom_reports': host['report_count'],
                      'sorgenfrey_selected_theorems_covered': len(sorgenfrey['theorem_names'])}, indent=2))


if __name__ == '__main__':
    check()
