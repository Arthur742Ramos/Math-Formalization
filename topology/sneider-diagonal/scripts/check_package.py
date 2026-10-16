"""Validate frozen package bytes and recorded transitive axioms, without executing Lean."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
NAMES = ['Sneider.' + n for n in [
    'exists_closed_countable_nhds_basis_of_isGδ',
    'nhdsSet_isCountablyGenerated_of_isGδ', 'isGdelta_diagonal',
    'exists_closed_diagonal_basis', 'metrizableSpace_of_isGdelta_diagonal',
    'metrizable_iff_isGdelta_diagonal', 'exists_compatibleMetric']]
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUTHORS = ['Arthur Freitas Ramos', 'David Barros Hulak',
    'Ruy Jose Guerra Barretto de Queiroz']
MAINTAINERS = ['Arthur Freitas Ramos', 'David Barros Hulak',
    'Ruy Jose Guerra Barretto de Queiroz']


def check(log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert manifest['name'] == 'sneiderDiagonal'
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert mathlib['rev'] == mathlib['inputRev'] == PIN
    for package in manifest['packages']:
        assert package['type'] == 'git'
        assert re.fullmatch(r'[0-9a-f]{40}', package['rev'])
        assert re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', package['url'])
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    assert lake['name'] == manifest['name']
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config == {'challenge_module': 'SDChallenge', 'solution_module': 'SDSolution',
        'theorem_names': NAMES, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    challenge = (ROOT / 'SDChallenge.lean').read_bytes()
    assert challenge == (ROOT / 'SneiderDiagonal.lean').read_bytes()
    assert len(challenge.splitlines()) <= 1000 and len(challenge) <= 100 * 1024
    imports = re.findall(rb'^public import (\S+)$', challenge, re.M)
    assert imports and all(i.startswith(b'Mathlib.') for i in imports)
    assert not re.search(rb'^(?!public )import\b', challenge, re.M)
    assert (ROOT / 'SDSolution.lean').read_text() == 'module\n\npublic import SneiderDiagonal\n'
    assert 'import SDChallenge' in (ROOT / 'ChallengeTests.lean').read_text()
    assert 'import SDSolution' in (ROOT / 'SemanticTests.lean').read_text()
    meta = json.loads((ROOT / 'formalization.yaml').read_text())
    assert meta['project']['name'] == "Sneider's Gδ-diagonal metrization theorem"
    assert meta['project']['authors'] == AUTHORS
    assert meta['project']['responsible_maintainers'] == MAINTAINERS
    assert meta['status']['attribution_status'].startswith('confirmed:')
    assert meta['project']['license'] == 'Apache-2.0'
    assert meta['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54E35', '54D30']}
    assert meta['status']['sorry_count'] == meta['status']['sorry_in_definitions'] == 0
    assert set(meta['status']['axioms']) == AXIOMS
    assert meta['sources'][0]['id'] == 'https://arxiv.org/pdf/math/9910153v1'
    readme = (ROOT / 'README.md').read_text()
    assert all(name in readme for name in AUTHORS + MAINTAINERS)
    assert 'separately confirmed roles' in readme
    assert 'no human review is' in readme
    lean_files = []
    for path in ROOT.rglob('*.lean'):
        if '.lake' in path.relative_to(ROOT).parts:
            continue
        assert not path.is_symlink()
        body = path.read_text()
        assert re.search(r'^module\s*$', body, re.M), str(path)
        assert len(body.splitlines()) <= 10000, str(path)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', body), str(path)
        lean_files.append(path.name)
    reports = {}
    body = pathlib.Path(log).read_text()
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", body):
        assert name not in reports
        reports[name] = {a.strip() for a in values.split(',') if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", body):
        assert name not in reports
        reports[name] = set()
    assert set(reports) == set(NAMES), sorted(reports)
    assert all(values <= AXIOMS for values in reports.values())
    hashes = {}
    record = ROOT / 'verification/source-hashes.json'
    for path in sorted(ROOT.rglob('*')):
        if '.lake' in path.relative_to(ROOT).parts or '__pycache__' in path.parts:
            continue
        if path.is_file() and path != record:
            assert not path.is_symlink()
            hashes[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if write:
        record.write_text(json.dumps(hashes, indent=2) + '\n')
    else:
        assert json.loads(record.read_text()) == hashes, 'Frozen source hash mismatch'
    print(json.dumps({'status': 'pass', 'selected_theorems': len(NAMES),
        'selected_definitions': 0, 'axiom_declarations': len(reports),
        'submission_ready': False, 'pending': [
            'canonical full mechanical preflight', 'canonical Challenge rendering'],
        'challenge_lines': len(challenge.splitlines()), 'challenge_bytes': len(challenge),
        'lean_sources': sorted(lean_files), 'source_files_hashed': len(hashes),
        'scope': 'Static package consistency and supplied axiom log; no build or Comparator.'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--axiom-log', default=str(ROOT / 'verification/local-axioms.txt'))
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
