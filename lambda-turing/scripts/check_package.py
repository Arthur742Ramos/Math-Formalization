"""Check packaging structure only; this does not validate Lean or Palomar readiness."""
from pathlib import Path
import json
import hashlib
import re
import tomllib
from lean_imports import header_imports

ROOT = Path(__file__).resolve().parents[1]
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
AUTHORS = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy José Guerra Barretto de Queiroz']
THEOREMS = [
    'LambdaTuring.lambdaComputable_iff_unaryMachine',
    'LambdaTuring.packagedLambdaToMachine_correct',
    'LambdaTuring.packagedLambdaToMachine_no_result',
    'LambdaTuring.Machine.machineToLambda_correct',
    'LambdaTuring.Machine.machineToLambda_no_result',
    'LambdaTuring.explicitPackagedTranslations_correct',
]
# Only deliberately unspecified translator values are Comparator definition targets.
# Fixed model definitions remain ordinary dependencies checked through theorems.
DEFINITIONS = [
    'LambdaTuring.packagedLambdaToMachine', 'LambdaTuring.Machine.machineToLambda',
]

lake = tomllib.loads((ROOT / 'lakefile.toml').read_text(encoding='utf-8'))
lock = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
metadata = json.loads((ROOT / 'formalization.yaml').read_text(encoding='utf-8'))
config = json.loads((ROOT / 'comparator.json').read_text(encoding='utf-8'))
assert lake['name'] == lock['name'] == 'LambdaTuring'
assert (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.35.0-rc2'
assert lake['require'] == [{'name': 'mathlib', 'git': 'https://github.com/leanprover-community/mathlib4.git', 'rev': PIN}]
assert len(lock['packages']) == 9
mathlib = [p for p in lock['packages'] if p['name'] == 'mathlib']
assert len(mathlib) == 1 and mathlib[0]['rev'] == mathlib[0]['inputRev'] == PIN
assert metadata['project']['authors'] == AUTHORS and metadata['project']['license'] == 'Apache-2.0'
assert isinstance(metadata['project']['responsible_maintainers'], list)
assert isinstance(metadata['review']['status'], str)
assert config['challenge_module'] == 'LambdaTuringChallenge' and config['solution_module'] == 'LambdaTuringSolution'
assert config['theorem_names'] == THEOREMS and config['definition_names'] == DEFINITIONS
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
challenge = (ROOT / 'LambdaTuringChallenge.lean').read_text(encoding='utf-8')
challenge_imports = header_imports(challenge)
if any(name == 'LambdaTuring' or name.startswith('LambdaTuring.') for name in challenge_imports):
    raise SystemExit('Challenge imports submitted project source; Palomar requires an allowed independent Challenge closure')
if any(name.split('.', 1)[0] not in {'Init', 'Lean', 'Std', 'Mathlib', 'Cslib', 'TauCeti'} for name in challenge_imports):
    raise SystemExit('Challenge has a direct import outside this conservative core/Mathlib/CSLib/Tau Ceti set')
pending = ['LambdaTuringSolution']
visited = set()
while pending:
    module = pending.pop()
    if module in visited:
        continue
    visited.add(module)
    if module == 'LambdaTuringChallenge':
        raise SystemExit('Solution imports the Challenge statement scaffold')
    path = ROOT / (module.replace('.', '/') + '.lean')
    if path.is_file():
        body = path.read_text(encoding='utf-8')
        pending.extend(header_imports(body))
    elif module == 'LambdaTuring' or module.startswith('LambdaTuring.'):
        raise SystemExit(f'Local Solution import has no source file: {module}')
solution = (ROOT / 'LambdaTuringSolution.lean').read_text(encoding='utf-8')
assert solution.split('-/\n', 1)[1] == ('module\npublic import LambdaTuring.DirectLambdaToMachine\n'
                                        'public meta import LambdaTuring.DirectLambdaToMachine\n')
for name in ('LambdaTuringChallengeTests', 'LambdaTuringSemanticTests', 'LambdaTuringAxiomAudit', 'LambdaTuringTranslationCodegen'):
    assert name in lake['defaultTargets'] and (ROOT / (name + '.lean')).is_file()
for file in ROOT.rglob('*.lean'):
    assert not file.is_symlink(), file
    text = file.read_text(encoding='utf-8')
    assert re.search(r'^module\s*$', text, re.M), file
    if file == ROOT / 'LambdaTuringChallenge.lean':
        assert len(re.findall(r'^\s+sorry\s*$', text, re.M)) == 8
        assert not re.search(r'\badmit\b|^\s*axiom\s', text, re.M), file
    else:
        assert not re.search(r'\b(?:sorry|admit)\b|^\s*axiom\s', text, re.M), file
for name in config['theorem_names'] + config['definition_names']:
    for test in ('LambdaTuringChallengeTests.lean', 'LambdaTuringSemanticTests.lean', 'LambdaTuringAxiomAudit.lean'):
        assert name in (ROOT / test).read_text(encoding='utf-8'), (name, test)
assert hashlib.sha256((ROOT / 'LICENSE').read_bytes()).hexdigest() == '5f3751276afe718ffa78ec1fc61490d4185712554bcb6a90059416dc424ce9a6'
assert (ROOT / 'THIRD_PARTY_NOTICES.md').is_file()
print('Static package structure: pass. No Lean build, comparator, current schema or license review was performed.')
if not metadata['project']['responsible_maintainers']:
    print('Open: maintainer designation.')
print('Open: current registry schema, exact-source verification and independent review.')
