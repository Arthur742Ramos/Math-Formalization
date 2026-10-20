"""Check source consistency and supplied axiom evidence, without claiming canonical verification."""
import argparse
import hashlib
import json
import pathlib
import re
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
THEOREMS = ['CategoryGame.exists_jointPlay', 'CategoryGame.not_both_winning', 'CategoryGame.residual_has_dense_open_sequence', 'CategoryGame.second_winning_of_isMeagre', 'CategoryGame.open_residual_witness', 'CategoryGame.first_winning_of_open_residual', 'CategoryGame.first_winning_of_nonmeagre', 'CategoryGame.determined_of_baireMeasurable', 'CategoryGame.first_winning_iff_nonmeagre', 'CategoryGame.second_winning_iff_isMeagre']
FIXED_MODEL_DEFINITIONS = ['CategoryGame.OpenMove', 'CategoryGame.history', 'CategoryGame.FollowsFirst', 'CategoryGame.FollowsSecond', 'CategoryGame.FirstWins', 'CategoryGame.SecondWins', 'CategoryGame.Determined']
ROLES = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check(axiom_log, write):
    assert (ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
    lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert lake['name'] == lock['name'] == 'banachMazurCategory'
    assert lake['require'] == [{'name': 'mathlib', 'git':
        'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
    assert len(lock['packages']) == 9
    for d in lock['packages']:
        assert d['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', d['rev'])
        assert re.fullmatch(r'https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?', d['url'])
    mathlib = next(d for d in lock['packages'] if d['name'] == 'mathlib')
    assert mathlib['rev'] == mathlib['inputRev'] == PIN
    config = json.loads((ROOT / 'comparator.json').read_text())
    assert config == {'challenge_module': 'CGChallenge',
        'solution_module': 'CGSolution', 'theorem_names': THEOREMS,
        'definition_names': [], 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice']}
    proof = (ROOT / 'CategoryGame.lean').read_bytes()
    assert proof == (ROOT / 'CGChallenge.lean').read_bytes()
    assert len(proof) < 100 * 1024 and len(proof.splitlines()) < 1000
    assert re.findall(rb'^public import (\S+)$', proof, re.M) == [
        b'Mathlib.Topology.Baire.BaireMeasurable', b'Mathlib.Topology.MetricSpace.Bounded',
        b'Mathlib.Analysis.SpecificLimits.Basic']
    assert (ROOT / 'CGSolution.lean').read_text() == 'module\npublic import CategoryGame\n'
    for filename, entry in [('ChallengeTests.lean', 'CGChallenge'),
                             ('SemanticTests.lean', 'CGSolution')]:
        body = (ROOT / filename).read_text()
        assert 'import ' + entry in body
        assert not ('import CGChallenge' in body and 'import CGSolution' in body)
    assert all(n in (ROOT / 'ChallengeTests.lean').read_text() for n in THEOREMS + FIXED_MODEL_DEFINITIONS)
    for f in ROOT.glob('*.lean'):
        assert not f.is_symlink()
        body = f.read_text()
        assert re.search(r'^module\s*$', body, re.M)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by)\b', body), f.name
        assert all(name in body for name in ROLES) if f.name in {'CategoryGame.lean', 'CGChallenge.lean'} else True
    metadata = json.loads((ROOT / 'formalization.yaml').read_text())
    assert metadata["project"]["name"] == "Banach–Mazur determinacy for Baire-property targets"
    assert metadata['project']['authors'] == metadata['project']['responsible_maintainers'] == ROLES
    assert metadata['project']['license'] == 'Apache-2.0'
    assert metadata['classification'] == {'arxiv': ['math.GN'], 'msc2020': ['54E52', '91A44', '03E15']}
    assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
    assert set(metadata['status']['axioms']) == ALLOWED
    assert all(name in (ROOT / 'README.md').read_text() for name in ROLES)
    assert 'No novelty' in metadata['sources'][0]['note']
    material = json.loads((ROOT / 'verification/material-imported-definitions.json').read_text())
    names = set(material['required_declarations'])
    assert {'BaireMeasurableSet','residual','IsMeagre','MetricSpace','CompleteSpace','Cauchy','IsComplete','IsOpen','Set.Nonempty','TopologicalSpace'} <= names
    assert material['schema_version'] == 2
    assert set(material['required_declarations']) == names
    assert len(material['material_declarations']) == len(names)
    assert {d['name'] for d in material['material_declarations']} == names
    assert material['dependency']['commit'] == PIN
    assert material['documentation'] == 'MATERIAL-DEFINITIONS.md'
    assert (ROOT / material['documentation']).is_file()
    for bridge in material['checked_bridge_modules']:
        assert bridge['path'] in ['ChallengeTests.lean', 'SemanticTests.lean']
        assert hashlib.sha256((ROOT / bridge['path']).read_bytes()).hexdigest() == bridge['sha256']
    assert {b['path'] for b in material['checked_bridge_modules']} == {'ChallengeTests.lean', 'SemanticTests.lean'}
    assert 'MATERIAL-DEFINITIONS.md' in (ROOT / 'README.md').read_text()
    core = json.loads((ROOT / 'verification/core-definitions.json').read_text())
    assert core['compiler_commit'] == '11acb17ec6b07a8f9e9173e6845197929540936b'
    assert core['path'] == 'src/Init/Prelude.lean'
    assert core['sha256'] == 'cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39'
    assert [x['name'] for x in core['excerpts']] == ['List', 'List.length']
    core_doc = (ROOT / 'CORE-DEFINITIONS.md').read_text()
    for excerpt in core['excerpts']:
        assert excerpt['url'] == core['repository'] + '/blob/' + core['compiler_commit'] + '/' + core['path'] + f"#L{excerpt['first_line']}-L{excerpt['last_line']}"
        assert hashlib.sha256(excerpt['text'].encode()).hexdigest() == excerpt['sha256']
        assert excerpt['text'] in core_doc and excerpt['url'] in core_doc
    assert core['sha256'] in core_doc and core['git_blob_sha1'] in core_doc
    text = pathlib.Path(axiom_log).read_text()
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        assert name not in reports
        reports[name] = {x.strip() for x in axioms.split(',') if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        assert name not in reports
        reports[name] = set()
    assert set(reports) == set(THEOREMS + FIXED_MODEL_DEFINITIONS)
    expected = {n: ALLOWED for n in THEOREMS}
    expected['CategoryGame.exists_jointPlay'] = set()
    expected['CategoryGame.not_both_winning'] = set()
    assert all(reports[n] == expected[n] for n in THEOREMS)
    assert all(reports[n] == set() for n in FIXED_MODEL_DEFINITIONS)
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
        'definition_holes': 0, 'fixed_model_definitions': len(FIXED_MODEL_DEFINITIONS), 'axiom_reports': len(reports),
        'source_files_hashed': len(hashes), 'challenge_lines': len(proof.splitlines()),
        'scope': 'Static package consistency, retained material-definition inventory and supplied transitive axiom evidence. Canonical full, rendering, editorial and registry stages require separate exact-source receipts.',
        'intake_authorized': False}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--axiom-log', type=pathlib.Path, default=ROOT / 'verification/local-axioms.txt')
    parser.add_argument('--write-hashes', action='store_true')
    args = parser.parse_args()
    check(args.axiom_log, args.write_hashes)
