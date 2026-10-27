"""Validate a narrowly scoped status-only evidence reuse; never certify a fresh run."""
import argparse
import json
import pathlib
import subprocess

from check_release_packet import bind_full, check_archive, check_status, require, sha, snapshot

ALLOWED_STATUS = {('status', 'known_gaps'), ('review', 'notes')}
ALLOWED_FILES = {'README.md', 'formalization.yaml'}


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate metadata key: ' + key)
        result[key] = value
    return result


def _metadata(data):
    value = json.loads(data.decode('utf-8'), object_pairs_hook=_unique_object)
    require(isinstance(value, dict), 'Metadata must be a JSON object')
    for outer, inner in ALLOWED_STATUS:
        require(isinstance(value.get(outer), dict) and isinstance(value[outer].get(inner), str),
                'Missing text status field: ' + outer + '.' + inner)
    return value


def classify(old, new, old_modes, new_modes):
    """Reject every package change except README and two metadata text fields."""
    require(set(old) == set(new) == set(old_modes) == set(new_modes), 'Package file set changed')
    require(old_modes == new_modes, 'Package file mode changed')
    require(all(mode in {'100644', '100755'} for mode in old_modes.values()),
            'Non-regular package entry')
    changed = {name for name in old if old[name] != new[name]}
    require(changed and changed <= ALLOWED_FILES, 'Proof, configuration, pin, or other package file changed')
    before, after = _metadata(old['formalization.yaml']), _metadata(new['formalization.yaml'])
    for outer, inner in ALLOWED_STATUS:
        before[outer][inner] = after[outer][inner]
    require(before == after, 'Metadata changed outside permitted status text')
    return sorted(changed)


def modes(root, commit, project):
    output = subprocess.check_output(['git', '-C', str(root), 'ls-tree', '-r', '-z', commit + ':' + project])
    result = {}
    for entry in output.split(b'\0'):
        if not entry:
            continue
        header, name = entry.split(b'\t', 1)
        mode, kind, _oid = header.decode('ascii').split(' ')
        require(kind == 'blob', 'Non-blob package entry')
        result[name.decode('utf-8')] = mode
    return result


def _read_authenticated(path, expected, label):
    require(isinstance(expected, str) and len(expected) == 64, label + ' expected digest missing')
    data = pathlib.Path(path).read_bytes()
    require(sha(data) == expected, label + ' digest mismatch')
    return json.loads(data)


def check(root, packet, archive, historical_commit, full_path, full_sha,
          full_adapter_path, full_adapter_sha, render_path, render_sha,
          render_adapter_path, render_adapter_sha, review_path, review_sha,
          scope_path, scope_sha):
    hold = packet.get('submission_hold', {})
    require(isinstance(hold, dict) and type(hold.get('active', False)) is bool, 'Invalid submission hold')
    require(not hold.get('active', False), 'Submission hold is active')
    fields = packet.get('proposed_submission_fields', packet.get('submission_fields', packet))
    project, corrected = fields['project_path'], fields['commit']
    ledger = pathlib.Path(root) / 'RELEASE-HANDOFFS.json'
    if ledger.exists():
        for row in json.loads(ledger.read_text())['blocked_sources']:
            require((project, corrected) != (row['path'], row['source_commit']),
                    'Blocked or superseded source: ' + row['reason'])
    require(historical_commit != corrected, 'Historical and corrected commits must differ')
    old, new = snapshot(root, historical_commit, project), snapshot(root, corrected, project)
    changes = classify(old, new, modes(root, historical_commit, project), modes(root, corrected, project))
    check_status(root, corrected, project)
    check_archive(pathlib.Path(archive).read_bytes(), new)
    full = _read_authenticated(full_path, full_sha, 'Historical full report')
    render = _read_authenticated(render_path, render_sha, 'Historical render report')
    fa = _read_authenticated(full_adapter_path, full_adapter_sha, 'Historical full adapter')
    ra = _read_authenticated(render_adapter_path, render_adapter_sha, 'Historical render adapter')
    review = _read_authenticated(review_path, review_sha, 'Historical independent review')
    scope = _read_authenticated(scope_path, scope_sha, 'Independent boundary review')
    historical_fields = dict(fields, commit=historical_commit)
    bind_full(full, historical_fields, old)
    pipeline = packet['pipeline_commit']
    for adapter, mode, report_sha, count in [(fa, 'full', full_sha, 3), (ra, 'render', render_sha, 2)]:
        require(adapter.get('status') == 'pass' and adapter.get('mode') == mode and
                adapter.get('commit') == historical_commit and adapter.get('pipeline_commit') == pipeline and
                adapter.get('report_sha256') == report_sha and len(adapter.get('steps', [])) == count and
                all(step.get('exit_code') == 0 for step in adapter['steps']), 'Historical adapter mismatch: ' + mode)
    require(render.get('status') == 'pass' and render.get('stage') == 'complete' and render.get('errors') == [],
            'Historical rendering did not pass')
    src = render['source']
    for key, expected in [('repository', fields['repository']), ('commit', historical_commit),
                          ('project_path', project), ('challenge_path', project + '/' + json.loads(old['comparator.json'])['challenge_module'].replace('.', '/') + '.lean'),
                          ('solution_path', project + '/' + json.loads(old['comparator.json'])['solution_module'].replace('.', '/') + '.lean'),
                          ('comparator_config_path', fields['comparator_config_path']),
                          ('lakefile_path', project + '/lakefile.toml'), ('lean_toolchain_path', project + '/lean-toolchain')]:
        require(src.get(key) == expected, 'Historical render source mismatch: ' + key)
    challenge = src['challenge_path'][len(project) + 1:]
    require(src.get('challenge_sha256') == sha(old[challenge]) and render.get('renderer_commit') == pipeline,
            'Historical render input or pipeline mismatch')
    require(render.get('format') == 'verso-html' and render.get('entrypoint') == 'Challenge/index.html' and
            render.get('lean_toolchain') == old['lean-toolchain'].decode().strip(), 'Historical rendering format or toolchain mismatch')
    require(render.get('surface', {}).get('declarations') == json.loads(old['comparator.json'])['theorem_names'] + json.loads(old['comparator.json'])['definition_names'],
            'Historical render surface mismatch')
    require(review.get('status') == 'pass_final_independent_release_review' and
            review.get('source_commit') == historical_commit and review.get('full_report_sha256') == full_sha and
            review.get('render_report_sha256') == render_sha, 'Historical independent review mismatch')
    tree = lambda commit: subprocess.check_output(['git', '-C', str(root), 'rev-parse', commit + ':' + project], text=True).strip()
    require(scope.get('status') == 'pass' and scope.get('kind') == 'independent-source-boundary-review' and
            scope.get('historical_commit') == historical_commit and scope.get('corrected_commit') == corrected and
            scope.get('historical_package_tree') == tree(historical_commit) and scope.get('corrected_package_tree') == tree(corrected) and
            scope.get('historical_full_report_sha256') == full_sha and scope.get('historical_render_report_sha256') == render_sha and
            scope.get('proof_boundary_reviewed') is True and scope.get('render_impact_reviewed') is True and
            isinstance(scope.get('reviewer'), str) and scope['reviewer'].strip() and
            isinstance(scope.get('findings'), list) and scope['findings'], 'Missing or mismatched independent boundary review')
    return {'status': 'conditional-pass', 'mode': 'status-only-evidence-reuse',
            'repository': fields['repository'], 'project_path': project,
            'historical_tested_commit': historical_commit, 'corrected_commit': corrected,
            'changed_files': changes, 'historical_full_report_sha256': full_sha,
            'historical_render_report_sha256': render_sha, 'corrected_metadata_sha256': sha(new['formalization.yaml']),
            'corrected_archive_sha256': sha(pathlib.Path(archive).read_bytes()),
            'current_source_full': 'not run', 'current_source_render': 'not run',
            'scope': 'Source and historical evidence bindings only; independent current-source review, historical artifact authentication, current service requirements, duplicate checks and any service verification remain separate.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', required=True)
    parser.add_argument('--archive', required=True)
    parser.add_argument('--historical-commit', required=True)
    for name in ('full', 'full-adapter', 'render', 'render-adapter', 'review', 'scope'):
        parser.add_argument('--' + name, required=True)
        parser.add_argument('--' + name + '-sha256', required=True)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[1]
    try:
        result = check(root, json.loads(pathlib.Path(args.packet).read_text()), args.archive, args.historical_commit,
                       args.full, args.full_sha256, args.full_adapter, args.full_adapter_sha256,
                       args.render, args.render_sha256, args.render_adapter, args.render_adapter_sha256,
                       args.review, args.review_sha256, args.scope, args.scope_sha256)
        print(json.dumps(result, indent=2))
    except (ValueError, KeyError, AssertionError, FileNotFoundError, subprocess.CalledProcessError) as error:
        print(json.dumps({'status': 'blocked', 'reason': str(error)}, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
