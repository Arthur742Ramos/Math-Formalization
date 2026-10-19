"""Check source consistency and supplied axiom evidence, without claiming canonical verification."""
import argparse
import hashlib
import json
import pathlib
import re
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
THEOREMS = ['KuratowskiUlam.' + n for n in ['hasCountablePiBase_of_secondCountable', 'eventually_isNowhereDense_sections', 'eventually_residual_sections', 'eventually_isMeagre_sections', 'isMeagre_iff_eventually_sections', 'residual_iff_eventually_sections', 'baireSpace_prod']]
DEFINITIONS = ['KuratowskiUlam.IsCountablePiBase', 'KuratowskiUlam.HasCountablePiBase']
ROLES = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check(axiom_log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert lake['name'] == lock['name'] == 'kuratowskiUlam'
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
    assert len(lock['packages']) == 9
    for d in lock['packages']:
        assert d['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', d['rev'])
        assert re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', d['url'])
    mathlib = next(d for d in lock['packages'] if d['name'] == 'mathlib')
    assert mathlib['rev'] == mathlib['inputRev'] == PIN
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config == {'challenge_module': 'KUChallenge',
        'solution_module': 'KUSolution', 'theorem_names': THEOREMS,
        'definition_names': DEFINITIONS, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    proof = (ROOT / 'KuratowskiUlam.lean').read_bytes()
    assert proof == (ROOT / 'KUChallenge.lean').read_bytes()
    assert len(proof) < 100 * 1024 and len(proof.splitlines()) < 1000
    assert re.findall(rb'^public import (\S+)$', proof, re.M) == [
        b'Mathlib.Topology.Baire.BaireMeasurable', b'Mathlib.Topology.Bases']
    assert (ROOT / 'KUSolution.lean').read_text() == 'module\n\npublic import KuratowskiUlam\n'
    for filename, entry in [('ChallengeTests.lean', 'KUChallenge'),
                             ('SemanticTests.lean', 'KUSolution')]:
        body = (ROOT / filename).read_text()
        assert 'import ' + entry in body
        assert not ('import KUChallenge' in body and 'import KUSolution' in body)
    assert all(n in (ROOT / 'ChallengeTests.lean').read_text() for n in THEOREMS + DEFINITIONS)
    for f in ROOT.glob('*.lean'):
        assert not f.is_symlink()
        body = f.read_text()
        assert re.search(r'^module\s*$', body, re.M)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', body), f.name
        assert all(name in body for name in ROLES) if f.name in {'KuratowskiUlam.lean', 'KUChallenge.lean'} else True
    metadata = json.loads((ROOT / 'formalization.yaml').read_text())
    assert metadata['project']['name'] == 'Kuratowski–Ulam category theorem for countable pi-base spaces'
    assert metadata['project']['authors'] == metadata['project']['responsible_maintainers'] == ROLES
    assert metadata['project']['license'] == 'Apache-2.0'
    assert metadata['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54E52', '54B10']}
    assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
    assert set(metadata['status']['axioms']) == ALLOWED
    assert all(name in (ROOT / 'README.md').read_text() for name in ROLES)
    assert 'No novelty' in metadata['sources'][0]['note']
    text = pathlib.Path(axiom_log).read_text()
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        assert name not in reports
        reports[name] = {x.strip() for x in axioms.split(',') if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        assert name not in reports
        reports[name] = set()
    assert set(reports) == set(THEOREMS + DEFINITIONS)
    assert all(reports[n] == ALLOWED for n in THEOREMS)
    assert all(reports[n] == set() for n in DEFINITIONS)
    record = ROOT / 'verification/source-hashes.json'
    hashes = {}
    for f in sorted(ROOT.rglob('*')):
        relative = f.relative_to(ROOT)
        if '.lake' in relative.parts or '__pycache__' in relative.parts or f == record:
            continue
        if f.is_file():
            assert not f.is_symlink(), relative
            hashes[relative.as_posix()] = hashlib.sha256(f.read_bytes()).hexdigest()
    if write:
        record.write_text(json.dumps(hashes, indent=2) + '\n')
    else:
        assert json.loads(record.read_text()) == hashes, 'Frozen source hash mismatch'
    print(json.dumps({'status': 'pass', 'theorems': len(THEOREMS),
        'definitions': len(DEFINITIONS), 'axiom_reports': len(reports),
        'source_files_hashed': len(hashes), 'challenge_lines': len(proof.splitlines()),
        'scope': 'Static package consistency and supplied transitive axiom evidence. Canonical full, rendering, editorial and registry stages require separate exact-source receipts.',
        'intake_authorized': False}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--axiom-log', type=pathlib.Path, default=ROOT / 'verification/local-axioms.txt')
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
