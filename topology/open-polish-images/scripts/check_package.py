"""Check exact ordinary preparation evidence; never claim canonical verification."""
import argparse
import hashlib
import json
import pathlib
import re
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
NAMES = ['OpenPolish.' + n for n in ['imageStrategy_winning', 'strong_image',
    'completelyMetrizable_image', 'polish_image', 'polish_image_of_t3']]
FIXED = ['StrongChoquet.' + n for n in ['Move', 'Strategy', 'history', 'Follows', 'Winning', 'Strong']]
ROLES = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
SHA = lambda b: hashlib.sha256(b).hexdigest()


def check(axiom_log=None, write=False):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert lake['name'] == lock['name'] == 'openPolishImages'
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
    assert len(lock['packages']) == 9
    for p in lock['packages']:
        assert p['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', p['rev'])
    assert SHA(json.dumps(lock['packages'], sort_keys=True).encode()) == '538eb518cfbacb38fe44252338c3269c98131d4984cc5955741375ccb5ecd617', 'Dependency pins changed'
    cfg = json.loads((ROOT / 'comparator.json').read_text())
    assert cfg == {'challenge_module': 'OPChallenge', 'solution_module': 'OPSolution',
        'theorem_names': NAMES, 'definition_names': [],
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    proof = (ROOT / 'OpenPolish.lean').read_bytes()
    assert proof == (ROOT / 'OPChallenge.lean').read_bytes()
    imports = re.findall(r'^(?:public\s+)?import\s+(\S+)', proof.decode(), re.M)
    assert set(imports) == {'Mathlib.Topology.MetricSpace.Polish',
        'Mathlib.Topology.MetricSpace.Completion', 'Mathlib.Topology.GDelta.MetrizableSpace',
        'Mathlib.Topology.Compactness.Lindelof', 'Mathlib.Topology.Metrizable.Urysohn'}, \
        'Protected Challenge must import only the five pinned Mathlib modules'
    foundation_body = (ROOT / 'StrongChoquetFoundation.lean').read_text().split('public section\n', 1)[1]
    assert foundation_body in proof.decode(), 'Attributed foundation declaration body changed or omitted'
    assert len(proof.splitlines()) <= 1000 and len(proof) <= 100 * 1024
    assert SHA((ROOT / 'StrongChoquetFoundation.lean').read_bytes()) == (
        '3d22c5f7f5af43d1a1cb40d58f4cb2b1c1b5d217a17f62269d26225baaddbcdb')
    assert (ROOT / 'OPSolution.lean').read_text() == 'module\npublic import OpenPolish\n'
    for f in ROOT.glob('*.lean'):
        assert not f.is_symlink()
        text = f.read_text()
        assert re.search(r'^module\s*$', text, re.M)
        assert len(text.splitlines()) <= 10000
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', text), f.name
    for filename, entry in [('ChallengeTests.lean', 'OPChallenge'), ('SemanticTests.lean', 'OPSolution')]:
        text = (ROOT / filename).read_text()
        assert 'public import ' + entry in text
        assert not ('public import OPChallenge' in text and 'public import OPSolution' in text)
        assert all(n in text for n in NAMES + FIXED)
        assert 'section SurjectivityMatters' in text and 'section PointConstraint' in text
        assert 'section LegalDoesNotMeanWinning' in text
    metadata = json.loads((ROOT / 'formalization.yaml').read_text())
    assert metadata['project']['name'] == 'Continuous open images of Polish spaces'
    assert metadata['project']['authors'] == metadata['project']['responsible_maintainers'] == ROLES
    assert metadata['project']['license'] == 'Apache-2.0'
    assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
    assert set(metadata['status']['axioms']) == ALLOWED
    for role in ROLES:
        assert role in (ROOT / 'README.md').read_text()
    assert 'No novelty' in metadata['sources'][0]['note']
    material = json.loads((ROOT / 'verification/material-imported-definitions.json').read_text())
    required = {'Continuous', 'IsOpenMap', 'Topology.IsOpenQuotientMap', 'RegularSpace', 'T3Space',
        'PolishSpace', 'IsCompletelyMetrizableSpace', 'MetrizableSpace', 'SecondCountableTopology',
        'Set.image', 'Set.preimage', 'Set.inter'}
    assert required <= set(material['required_declarations'])
    assert len(material['required_declarations']) == len(set(material['required_declarations'])) == 62
    assert {b['path'] for b in material['checked_bridge_modules']} == {'ChallengeTests.lean', 'SemanticTests.lean'}
    for b in material['checked_bridge_modules']:
        assert SHA((ROOT / b['path']).read_bytes()) == b['sha256']
    for name in ['core-definitions.json', 'core-function-definitions.json']:
        core = json.loads((ROOT / 'verification' / name).read_text())
        assert core['compiler_commit'] == '11acb17ec6b07a8f9e9173e6845197929540936b'
        for e in core['excerpts']:
            assert SHA(e['text'].encode()) == e['sha256']
            assert e['text'] in (ROOT / 'CORE-DEFINITIONS.md').read_text()
    text = pathlib.Path(axiom_log or ROOT / 'verification/local-axioms.txt').read_text()
    reports = {}
    for line in text.splitlines():
        m = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        if m:
            assert m[1] not in reports
            reports[m[1]] = set(m[2].split(', ')) if m[2] else set()
        m = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if m:
            assert m[1] not in reports
            reports[m[1]] = set()
    assert set(reports) == set(NAMES + ['OpenPolish.imageStrategy'] + FIXED)
    assert all(a <= ALLOWED for a in reports.values())
    assert all(reports[n] == set() for n in FIXED)
    files = {p.relative_to(ROOT).as_posix(): SHA(p.read_bytes()) for p in sorted(ROOT.rglob('*'))
        if p.is_file() and '.lake' not in p.parts and '__pycache__' not in p.parts
        and p.relative_to(ROOT).as_posix() != 'verification/source-hashes.json'}
    path = ROOT / 'verification/source-hashes.json'
    if write:
        path.write_text(json.dumps(files, indent=2) + '\n')
    assert json.loads(path.read_text()) == files, 'Frozen package files changed'
    return {'status': 'pass', 'selected_theorems': NAMES, 'definition_holes': 0,
        'axiom_reports': len(reports), 'material_meanings': 62,
        'source_files': len(files), 'canonical_full': 'separate exact-source receipt required',
        'scope': 'Static package and supplied axiom-log consistency only; no build, independent kernel, renderer or registry claim.'}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--axiom-log')
    p.add_argument('--write-hashes', action='store_true')
    a = p.parse_args()
    print(json.dumps(check(a.axiom_log, a.write_hashes), indent=2))
