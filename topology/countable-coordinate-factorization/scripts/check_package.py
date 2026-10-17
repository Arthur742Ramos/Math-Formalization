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
NAMES = ['CountableCoordinates.finite_coordinates_of_entourage', 'CountableCoordinates.countable_coordinates_of_uniformContinuous', 'CountableCoordinates.countable_coordinates_of_continuous', 'CountableCoordinates.restrict_refill', 'CountableCoordinates.uniformContinuous_refill', 'CountableCoordinates.exists_countable_uniform_factorization', 'CountableCoordinates.exists_countable_continuous_factorization', 'CountableCoordinates.factor_unique', 'CountableCoordinates.exists_common_countable_factorization', 'CountableCoordinates.nontrivial_subset_of_injective', 'CountableCoordinates.countable_nontrivial_of_continuous_injective', 'CountableCoordinates.continuous_refill', 'CountableCoordinates.compact_product_metrizable_iff']
DEFINITIONS = ['CountableCoordinates.refill']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AUTHORS = ['Arthur Freitas Ramos', 'David Barros Hulak',
    'Ruy Jose Guerra Barretto de Queiroz']
MAINTAINERS = ['Arthur Freitas Ramos', 'David Barros Hulak',
    'Ruy Jose Guerra Barretto de Queiroz']


def check(log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert manifest['name'] == 'countableCoordinateFactorization'
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
    assert config == {'challenge_module': 'CCChallenge', 'solution_module': 'CCSolution',
        'theorem_names': NAMES, 'definition_names': DEFINITIONS, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    challenge = (ROOT / 'CCChallenge.lean').read_bytes()
    assert challenge == (ROOT / 'CountableCoordinateFactorization.lean').read_bytes()
    assert len(challenge.splitlines()) <= 1000 and len(challenge) <= 100 * 1024
    imports = re.findall(rb'^public import (\S+)$', challenge, re.M)
    assert imports and all(i.startswith(b'Mathlib.') for i in imports)
    assert not re.search(rb'^(?!public )import\b', challenge, re.M)
    assert (ROOT / 'CCSolution.lean').read_text() == 'module\n\npublic import CountableCoordinateFactorization\n'
    assert 'import CCChallenge' in (ROOT / 'ChallengeTests.lean').read_text()
    assert 'import CCSolution' in (ROOT / 'SemanticTests.lean').read_text()
    meta = json.loads((ROOT / 'formalization.yaml').read_text())
    assert meta['project']['name'] == "Countable-coordinate factorization for compact products"
    assert meta['project']['authors'] == AUTHORS
    assert meta['project']['responsible_maintainers'] == MAINTAINERS
    assert meta['status']['attribution_status'].startswith('confirmed:')
    assert meta['project']['license'] == 'Apache-2.0'
    assert meta['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54B10', '54C05', '54E35']}
    assert meta['status']['sorry_count'] == meta['status']['sorry_in_definitions'] == 0
    assert set(meta['status']['axioms']) == AXIOMS
    assert meta['sources'][0]['id'] == 'https://arxiv.org/pdf/1411.3173v1'
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
    assert set(reports) == set(NAMES + DEFINITIONS), sorted(reports)
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
        'selected_definitions': len(DEFINITIONS), 'axiom_declarations': len(reports),
        'submission_ready': False, 'pending': [
            'canonical full mechanical preflight', 'canonical Challenge rendering',
            'current registry-wide duplicate clearance'],
        'challenge_lines': len(challenge.splitlines()), 'challenge_bytes': len(challenge),
        'lean_sources': sorted(lean_files), 'source_files_hashed': len(hashes),
        'scope': 'Static package consistency and supplied axiom log; no build or Comparator.'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--axiom-log', default=str(ROOT / 'verification/local-axioms.txt'))
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
