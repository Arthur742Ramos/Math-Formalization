"""Check frozen source, module contracts, pins and supplied transitive-axiom evidence."""
import argparse
import hashlib
import json
import pathlib
import re
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
THEOREMS = ['Collectionwise.exists_open_expansion',
    'Collectionwise.exists_subordinate_expansion', 'Collectionwise.discrete_closed_iff',
    'Collectionwise.exists_discrete_expansion', 'Collectionwise.paracompact_hausdorff_collectionwise']
DEFINITIONS = ['Collectionwise.IsDiscreteFamily', 'Collectionwise.HasOpenExpansion']
ROLES = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def check(log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    assert lake['name'] == manifest['name'] == 'collectionwiseNormal'
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
    assert len(manifest['packages']) == 9
    for dependency in manifest['packages']:
        assert dependency['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', dependency['rev'])
        assert re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', dependency['url'])
    mathlib = next(d for d in manifest['packages'] if d['name'] == 'mathlib')
    assert mathlib['rev'] == mathlib['inputRev'] == PIN
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config == {'challenge_module': 'CollectionwiseChallenge',
        'solution_module': 'CollectionwiseSolution', 'theorem_names': THEOREMS,
        'definition_names': DEFINITIONS, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    proof = (ROOT / 'CollectionwiseNormal.lean').read_bytes()
    assert proof == (ROOT / 'CollectionwiseChallenge.lean').read_bytes()
    assert len(proof) < 100 * 1024 and len(proof.splitlines()) < 1000
    assert re.findall(rb'^public import (\S+)$', proof, re.M) == [
        b'Mathlib.Topology.Compactness.Paracompact']
    assert (ROOT / 'CollectionwiseSolution.lean').read_text() == 'module\n\npublic import CollectionwiseNormal\n'
    for file, entry in [('ChallengeTests.lean', 'CollectionwiseChallenge'),
                         ('SemanticTests.lean', 'CollectionwiseSolution')]:
        body = (ROOT / file).read_text()
        assert 'import ' + entry in body and all(name in body for name in THEOREMS + DEFINITIONS)
    for f in ROOT.glob('*.lean'):
        assert not f.is_symlink()
        body = f.read_text()
        assert re.search(r'^module\s*$', body, re.M)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', body), f.name
    meta = json.loads((ROOT / 'formalization.yaml').read_text())
    assert meta['project']['name'] == 'Paracompact expansion and collectionwise separation'
    assert meta['project']['authors'] == meta['project']['responsible_maintainers'] == ROLES
    assert meta['project']['license'] == 'Apache-2.0'
    assert meta['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54D15', '54D20']}
    assert meta['status']['sorry_count'] == meta['status']['sorry_in_definitions'] == 0
    assert set(meta['status']['axioms']) == ALLOWED
    history = json.loads((ROOT / 'verification/canonical-history.json').read_text())
    assert history['source_commit'] == '8ba7d5096d7d77a1e2f6e6f04ba70c85aed2a814'
    assert history['comparator_sha256'] == hashlib.sha256((ROOT / 'comparator.json').read_bytes()).hexdigest()
    assert history['lean_toolchain'] == (ROOT / 'lean-toolchain').read_text().strip()
    assert history['lockfile_sha256'] == hashlib.sha256((ROOT / 'lake-manifest.json').read_bytes()).hexdigest()
    assert history['full']['status'] == history['rendering']['status'] == 'pass'
    for account in [meta['status']['known_gaps'], (ROOT / 'README.md').read_text()]:
        assert history['source_commit'] in account and history['comparator_sha256'] in account
        assert str(history['full']['run_id']) in account and str(history['rendering']['run_id']) in account
        assert not re.search(r'canonical.{0,250}(?:remain unperformed|have not run|remain outstanding)', account, re.I | re.S)
    assert 'later' in meta['status']['known_gaps'] and 'exact-source' in meta['status']['known_gaps']
    assert meta['status']['attribution_status'].startswith('Campaign-authorized:')
    readme = (ROOT / 'README.md').read_text()
    assert all(name in readme for name in ROLES) and 'no human' in readme
    text = pathlib.Path(log).read_text()
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports = {name: {a.strip() for a in raw.split(',') if a.strip()} for name, raw in matches}
    assert len(matches) == len(reports) and set(reports) == set(THEOREMS + DEFINITIONS)
    assert all(values <= ALLOWED for values in reports.values())
    for name in THEOREMS:
        assert reports[name] == ALLOWED, (name, 'actual recorded theorem closure')
    for name in DEFINITIONS:
        assert reports[name] == {'propext', 'Quot.sound'}, (name, 'actual definition closure')
    record = ROOT / 'verification/source-hashes.json'
    hashes = {}
    for f in sorted(ROOT.rglob('*')):
        relative = f.relative_to(ROOT)
        if '.lake' in relative.parts or '__pycache__' in relative.parts or f == record:
            continue
        if f.is_file():
            assert not f.is_symlink(), str(relative)
            hashes[relative.as_posix()] = hashlib.sha256(f.read_bytes()).hexdigest()
    if write:
        record.write_text(json.dumps(hashes, indent=2) + '\n')
    else:
        assert json.loads(record.read_text()) == hashes, 'Frozen source hash mismatch'
    print(json.dumps({'status': 'pass', 'theorems': len(THEOREMS),
        'definitions': len(DEFINITIONS), 'selected_axiom_reports': len(reports),
        'source_files_hashed': len(hashes), 'challenge_lines': len(proof.splitlines()),
        'historical_canonical_verification': history,
        'current_source_full': 'Not established by this static check; require a source-bound external report',
        'registry_submission_ready': False,
        'scope': 'Static consistency and supplied axiom report only; no build or Comparator.'}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--axiom-log', default=str(ROOT / 'verification/local-axioms.txt'))
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
