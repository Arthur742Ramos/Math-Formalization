"""Check the frozen AU package and a recorded or freshly executed axiom log.

This performs no builds, network access, Comparator or registry operation.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
PREFIX = 'AlexandroffUrysohn.'
THEOREMS = [PREFIX + n for n in [
    'IsMetrizingSequence.exists_uniformity', 'pseudoMetrizable_iff',
    'metrizable_iff', 'exists_compatibleMetric']]
DEFINITIONS = [PREFIX + n for n in [
    'pointStar', 'IsOpenCover', 'IsMetrizingSequence', 'coverRelation']]
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TEAM = ['Arthur Freitas Ramos', 'David Barros Hulak',
        'Ruy Jose Guerra Barretto de Queiroz']


def check(log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert manifest['name'] == 'alexandroffUrysohn'
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert mathlib['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    assert lake['name'] == manifest['name']
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': mathlib['rev']}]
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config == {'challenge_module': 'AUChallenge', 'solution_module': 'AUSolution',
        'theorem_names': THEOREMS, 'definition_names': DEFINITIONS,
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    challenge = (ROOT / 'AUChallenge.lean').read_bytes()
    assert challenge == (ROOT / 'AlexandroffUrysohn.lean').read_bytes()
    assert len(challenge.splitlines()) <= 1000 and len(challenge) <= 100 * 1024
    imports = re.findall(rb'^public import (\S+)$', challenge, re.M)
    assert imports and all(i.startswith(b'Mathlib.') for i in imports)
    assert (ROOT / 'AUSolution.lean').read_text() == (
        'module\n\npublic import AlexandroffUrysohn\n')
    meta = json.loads((ROOT / 'formalization.yaml').read_text())
    assert meta['project']['name'] == 'Alexandroff–Urysohn cover metrization'
    assert meta['project']['authors'] == TEAM
    assert meta['project']['responsible_maintainers'] == TEAM
    assert meta['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54E35', '54E15']}
    assert meta['project']['license'] == 'Apache-2.0'
    assert meta['status']['sorry_count'] == meta['status']['sorry_in_definitions'] == 0
    assert set(meta['status']['axioms']) == AXIOMS
    readme = (ROOT / 'README.md').read_text()
    assert all(name in readme for name in TEAM)
    assert 'no human review is claimed' in readme
    for path in ROOT.rglob('*.lean'):
        if '.lake' in path.relative_to(ROOT).parts:
            continue
        assert not path.is_symlink()
        body = path.read_text()
        assert re.search(r'^module\s*$', body, re.M), str(path)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', body), str(path)
        assert len(body.splitlines()) <= 10000
    # Every tracked Lean source, including unrelated packages, must meet intake
    # module/line rules; this reads those sources without modifying or building them.
    tracked = subprocess.check_output(['git', 'ls-files', '*.lean'],
        cwd=REPOSITORY, text=True).splitlines()
    for name in tracked:
        path = REPOSITORY / name
        assert not path.is_symlink(), name
        body = path.read_text()
        assert re.search(r'^module\s*$', body, re.M), name
        assert len(body.splitlines()) <= 10000, name
    reports = {}
    body = pathlib.Path(log).read_text()
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", body):
        assert name not in reports, name
        reports[name] = {a.strip() for a in values.split(',') if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", body):
        assert name not in reports, name
        reports[name] = set()
    assert len(reports) == 17, len(reports)
    assert all(name in reports for name in THEOREMS + DEFINITIONS)
    assert all(values <= AXIOMS for values in reports.values())
    assert all(not reports[name] for name in DEFINITIONS)
    hashes = {}
    for path in sorted(ROOT.rglob('*')):
        if '.lake' in path.relative_to(ROOT).parts or '__pycache__' in path.parts:
            continue
        if path.is_file() and path != ROOT / 'verification/source-hashes.json':
            assert not path.is_symlink()
            hashes[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    record = ROOT / 'verification/source-hashes.json'
    if write:
        record.write_text(json.dumps(hashes, indent=2) + '\n')
    else:
        assert json.loads(record.read_text()) == hashes, 'Package bytes differ from frozen hashes'
    print(json.dumps({'status': 'pass', 'selected_theorems': len(THEOREMS),
        'selected_definitions': len(DEFINITIONS), 'axiom_declarations': len(reports),
        'challenge_lines': len(challenge.splitlines()), 'challenge_bytes': len(challenge),
        'tracked_lean_headers_checked': len(tracked), 'source_files_hashed': len(hashes),
        'axiom_log': str(log), 'scope': 'Static package consistency and supplied axiom log; no build or Comparator.'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--axiom-log', default=str(ROOT / 'verification/local-axioms.txt'))
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
