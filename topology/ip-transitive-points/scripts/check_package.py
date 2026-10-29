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
    'IPTransitive.weak_mixing_infinite_hits',
    'IPTransitive.positive_pair_returns_yield_ip',
    'IPTransitive.residual_ip_transitive',
    'IPTransitive.exists_dense_Gdelta_ip_transitive',
]
assert c['challenge_module'] == 'IPChallenge' and c['solution_module'] == 'IPSolution'
assert c['theorem_names'] == names and c['definition_names'] == []
assert set(c['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
roles = ['Arthur Freitas Ramos', 'David Barros Hulak', 'Ruy Jose Guerra Barretto de Queiroz']
assert m['project']['authors'] == roles
assert m['project']['responsible_maintainers'] == roles
assert (p / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
packages = json.loads((p / 'lake-manifest.json').read_text(encoding='utf-8'))['packages']
assert next(x for x in packages if x['name'] == 'mathlib')['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55'
challenge = (p / 'IPChallenge.lean').read_bytes()
assert challenge == (p / 'IPTransitive.lean').read_bytes()
assert (p / 'IPSolution.lean').read_text(encoding='utf-8').startswith('module\npublic import IPTransitive\n')
for module, imported in [('SemanticChallenge', 'IPChallenge'), ('SemanticSolution', 'IPSolution')]:
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
print('Package consistency passed; canonical verification and independent review remain separate.')
