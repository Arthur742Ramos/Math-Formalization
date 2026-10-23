import argparse,json,pathlib,re,tomllib
p=pathlib.Path(__file__).resolve().parents[1]
a=argparse.ArgumentParser();a.add_argument('--axiom-log');a.parse_args()
cfg=json.loads((p/'comparator.json').read_text());meta=json.loads((p/'formalization.yaml').read_text())
assert cfg['challenge_module']=='KRChallenge' and cfg['solution_module']=='KRSolution'
assert cfg['theorem_names']==['KnasterReichbach.exists_homeomorph_extension']
assert cfg['definition_names']==[]
assert set(cfg['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
roles=['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert meta['project']['authors']==roles and meta['project']['responsible_maintainers']==roles
assert meta['status']['sorry_count']==meta['status']['sorry_in_definitions']==0
assert (p/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
lock=json.loads((p/'lake-manifest.json').read_text())
assert next(x for x in lock['packages'] if x['name']=='mathlib')['rev']=='065356127b1dc0016f66b7283ce0ce2c4055aa55'
for f in list(p.glob('*.lean'))+list((p/'KnasterReichbach').glob('*.lean')):
 s=f.read_text();assert re.search(r'^module$',s,re.M),f
 assert not re.search(r'\b(sorry|admit|axiom)\b',s),f
assert 'No refinement or extension existence premise is assumed' in (p/'README.md').read_text()
print(json.dumps({'status':'pass','scope':'Static package consistency only; not proof, kernel, canonical or release verification'}))
