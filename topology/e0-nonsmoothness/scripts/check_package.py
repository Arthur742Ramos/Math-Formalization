import json,pathlib,re
p=pathlib.Path(__file__).resolve().parents[1]
c=json.loads((p/'comparator.json').read_text());m=json.loads((p/'formalization.yaml').read_text())
assert c['theorem_names']==['EZero.finite_flip_mixing', 'EZero.zero_one', 'EZero.generically_constant', 'EZero.no_baire_reduction', 'EZero.no_borel_reduction'] and c['definition_names']==[]
assert set(c['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
assert m['project']['authors']==m['project']['responsible_maintainers']==['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert (p/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
assert next(x for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
for f in p.rglob('*.lean'):
 if '.lake' in f.parts:continue
 s=f.read_text();assert s.startswith('module\n'),f
 assert not re.search(r'\b(sorry|admit|axiom)\b',s),f
assert len((p/'E0Challenge.lean').read_text().splitlines())<=1000 and (p/'E0Challenge.lean').stat().st_size<=102400
print('Package consistency passed; exact-source canonical and independent review required separately.')
