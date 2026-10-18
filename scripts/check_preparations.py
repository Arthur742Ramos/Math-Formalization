"""Validate frozen preparations separately from the canonical-pass readiness ledger."""
import hashlib
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


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
        assert p['state'] == 'reviewed-preparation-not-submitted'
        source, tree = p['source_snapshot']['commit'], p['source_snapshot']['tree']
        assert re.fullmatch(r'[0-9a-f]{40}', source) and re.fullmatch(r'[0-9a-f]{40}', tree)
        for ref in [source, 'HEAD']:
            assert git('rev-parse', ref + ':' + path) == tree
        subprocess.run(['git', '-C', str(ROOT), 'merge-base', '--is-ancestor', source, 'HEAD'], check=True)
        package = ROOT / path
        for name, expected in p['source_files_sha256'].items():
            assert pathlib.Path(name).name == name
            assert hashlib.sha256((package / name).read_bytes()).hexdigest() == expected
        config = json.loads((package / 'comparator.json').read_text())
        meta = json.loads((package / 'formalization.yaml').read_text())
        assert p['theorem_names'] == config['theorem_names']
        assert p['definition_names'] == config['definition_names']
        assert p['authors'] == meta['project']['authors']
        assert p['responsible_maintainers'] == meta['project']['responsible_maintainers']
        assert p['canonical_full'] == p['rendering'] == 'unperformed'
        assert p['canonical_run'] is None and p['rendering_run'] is None
        assert p['registry_submission_ready'] is False and p['registry_intakes_by_this_task'] == 0
        assert p['existing_public_id'] is None
        assert p['fresh_runner_security_approval'] is False
        assert p['reviews']['kind'] == 'independent-internal-AI'
        assert p['reviews']['mathematical_source'] == p['reviews']['implementation'] == 'pass'
        for digest in p['reviews']['receipts_sha256'].values():
            assert re.fullmatch(r'[0-9a-f]{64}', digest)
        matching = [row for row in rows if '](' + path + ')' in row]
        assert len(matching) == 1 and 'Preparation; not submitted' in matching[0]
        assert p['name'] in matching[0]
        assert f'https://github.com/{data["repository"]}/tree/{source}/{path}' in matching[0]
        result = subprocess.run(['python3', 'scripts/check_package.py'], cwd=package,
                                capture_output=True, text=True)
        assert result.returncode == 0, (path, result.stdout, result.stderr)
    return seen
