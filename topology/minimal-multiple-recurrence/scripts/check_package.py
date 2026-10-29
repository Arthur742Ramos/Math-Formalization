"""Check package consistency only; this does not certify the Lean proof."""
import json
import pathlib
import re
import subprocess
import sys

if not __debug__:
    raise RuntimeError('Package consistency checks require Python assertions enabled')

p = pathlib.Path(__file__).resolve().parents[1]
c = json.loads((p / 'comparator.json').read_text(encoding='utf-8'))
m = json.loads((p / 'formalization.yaml').read_text(encoding='utf-8'))
names = [
    'MultipleRecurrence.minimal_multiple_recurrence_after',
    'MultipleRecurrence.residual_multiply_recurrent',
    'MultipleRecurrence.finite_multipliers_return',
    'MultipleRecurrence.exists_dense_Gdelta_multiply_recurrent',
]
assert c['challenge_module'] == 'RecurrenceChallenge' and c['solution_module'] == 'RecurrenceSolution'
assert c['theorem_names'] == names and c['definition_names'] == []
assert set(c['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
roles = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
assert m['project']['authors'] == roles
assert m['project']['responsible_maintainers'] == roles
assert (p / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
packages = json.loads((p / 'lake-manifest.json').read_text(encoding='utf-8'))['packages']
assert next(x for x in packages if x['name'] == 'mathlib')['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
challenge = (p / 'RecurrenceChallenge.lean').read_bytes()
assert challenge == (p / 'MultipleRecurrence.lean').read_bytes()
assert (p / 'RecurrenceSolution.lean').read_text(encoding='utf-8').startswith('module\npublic import MultipleRecurrence\n')
for module, imported in [('SemanticChallenge', 'RecurrenceChallenge'), ('SemanticSolution', 'RecurrenceSolution')]:
    assert (p / (module + '.lean')).read_text(encoding='utf-8').startswith('module\npublic import ' + imported + '\n')
for name in names:
    assert re.search(r'\btheorem\s+' + re.escape(name.split('.')[-1]) + r'\b', challenge.decode('utf-8'))
for f in p.glob('*.lean'):
    source = f.read_text(encoding='utf-8')
    assert re.search(r'(?m)^module\s*$', source), f
    assert not re.search(r'\b(sorry|admit|axiom)\b', source), f
assert len(challenge.splitlines()) <= 1000 and len(challenge) <= 102400
checker = p.parent.parent / 'scripts/check_imported_definitions.py'
subprocess.run([sys.executable, str(checker), '--project-path', str(p)], check=True)
assert 'Unable to print axioms' in (p / 'README.md').read_text(encoding='utf-8')
assert 'Unable to print axioms' in m['status']['known_gaps']
assert 'ade9847cd7cc7d131de2dac2ea8db1c03504f2fd' in m['status']['known_gaps']
for predicate in ['ForwardMinimal', 'MultiplyRecurrent']:
    assert re.search(r'(?m)^def ' + predicate + r'\b', challenge.decode('utf-8'))
print('Package consistency passed; canonical verification and independent review remain separate.')
