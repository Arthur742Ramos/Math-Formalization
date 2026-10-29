import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
dest = root / 'weak-mixing-cantor-chaos'
selections = {
    'mycielski-cantor-independent': [
        'TopologicalSpace', 'IsOpen', 'IsClosed', 'closure', 'Continuous',
        'Homeomorph', 'TopologicalSpace.induced', 'Filter', 'Equiv',
        'IsCompact', 'CompactSpace', 'Dense', 'Set.range', 'PolishSpace',
        'SecondCountableTopology', 'TopologicalSpace.IsCompletelyMetrizableSpace',
        'CompleteSpace', 'Cauchy', 'PerfectSpace', 'Preperfect', 'AccPt',
        'Topology.IsInducing', 'Topology.IsEmbedding', 'Topology.IsClosedEmbedding'],
    'ip-transitive-points': ['Nat.iterate', 'Set.Nonempty', 'IsTopologicalBasis',
                             'Set.Finite', 'T2Space', 'interior'],
    'weak-mixing-thick-multisensitivity': ['MetricSpace', 'PseudoMetricSpace',
        'UniformSpace', 'uniformity', 'Nontrivial'],
}
theorems = ['CantorChaos.cantor_dense_pair_orbits', 'CantorChaos.cantor_uniform_scrambled']
declarations = []
sources = {}
excerpts_by_name = {}
need = set()
for project, names in selections.items():
    data = json.loads((root / project / 'verification/material-imported-definitions.json').read_text(encoding='utf-8'))
    decls = {d['name']: d for d in data['material_declarations']}
    for name in names:
        d = dict(decls[name])
        d['used_by'] = theorems
        d['role'] = 'proof-dependency'
        if name in {'MetricSpace', 'PolishSpace', 'PerfectSpace', 'Nontrivial', 'Continuous', 'IsOpen', 'Set.Nonempty'}:
            d['role'] = 'hypothesis'
        if name in {'Topology.IsClosedEmbedding', 'Set.range', 'Dense'}:
            d['role'] = 'hypothesis-and-conclusion'
        d['dependency_expansion'] = d['dependency_expansion'].replace('The retained literal source and separately compiled class/field/equivalence bridges expand this meaning.', 'The retained literal source and class/field/equivalence bridges support this meaning; bridge compilation is a separate check.')
        d['proof_status'] = 'Pinned literal source excerpts retained; bridge compilation and independent completeness/fidelity review are separate gates.'
        declarations.append(d)
        need.add(d['definition_excerpt'])
        need.update(d['bridge_excerpts'])
    for src in data['source_files']:
        path = src['path']
        if path not in sources:
            sources[path] = dict(src, excerpts=[])
        else:
            for key in ('url', 'sha256', 'git_blob_sha1', 'upstream_header', 'license'):
                assert sources[path][key] == src[key], (path, key)
        for e in src['excerpts']:
            if e['name'] in excerpts_by_name:
                old_path, old = excerpts_by_name[e['name']]
                assert old_path == path and old == e, (e['name'], old_path, path)
            else:
                excerpts_by_name[e['name']] = (path, e)

# Definitions and meanings below are scoped to these selected theorems.
overrides = {
    'Set.Nonempty': 'A source or target open set contains a member; no IP-point predicate is involved.',
    'Set.Finite': 'Finite sets support removal of the finitely many orbit positions before a requested lower bound.',
    'T2Space': 'Hausdorff separation follows from the metric or Polish instances; it is not an additional main-theorem binder.',
    'IsTopologicalBasis': 'A countable basis of the square supplies the open targets for dense-orbit relations.',
    'Dense': 'A set meets every nonempty open set; DenseOrbit uses the dense range of the square orbit.',
    'Set.range': 'The image of a function, used both for orbit sequences and for the Cantor embedding image.',
    'MetricSpace': 'The supplied metric defines the output distances; it is explicitly assumed in the uniform-scrambling theorem.',
    'PseudoMetricSpace': 'The inherited metric structure supplies the distance function and its metric compatibility.',
    'PerfectSpace': 'The topology has no isolated points. The uniform theorem assumes Nontrivial before choosing the scale; the dense-pair theorem instead takes a nonempty open U.',
}
for declaration in declarations:
    name = declaration['name']
    if name in overrides:
        declaration['meaning'] = overrides[name]
        declaration['dependency_expansion'] = overrides[name]
    if name in {'MetricSpace', 'PseudoMetricSpace', 'Nontrivial', 'uniformity', 'UniformSpace'}:
        declaration['used_by'] = [theorems[1]]
declarations.append({
    'name': 'Dist', 'declaration_kind': 'class', 'role': 'conclusion',
    'used_by': [theorems[1]],
    'meaning': 'The distance function of the supplied metric measures both closeness and separation.',
    'dependency_expansion': 'Dist.dist is a real-valued function; MetricSpace and PseudoMetricSpace provide its metric laws.',
    'definition_excerpt': 'Dist', 'bridge_kind': 'class-fields', 'bridge_excerpts': ['Dist'],
    'proof_status': 'Pinned literal source retained; bridge compilation and independent review are separate gates.'
})
need.add('Dist')
for name in sorted(need):
    path, excerpt = excerpts_by_name[name]
    sources[path]['excerpts'].append(excerpt)
sources = {p: s for p, s in sources.items() if s['excerpts']}
modules = []
for name in ['SemanticChallenge', 'SemanticSolution']:
    filename = name + '.lean'
    modules.append({'module': name, 'path': filename,
                    'sha256': hashlib.sha256((dest / filename).read_bytes()).hexdigest()})
manifest = {
    'schema_version': 2,
    'dependency': {'name':'mathlib', 'repository':'https://github.com/leanprover-community/mathlib4',
                   'commit':'065356127b1dc0016f66b7283ce0ce2c4055aa55',
                   'lean_toolchain':'leanprover/lean4:v4.35.0-rc2'},
    'documentation':'MATERIAL-DEFINITIONS.md',
    'required_declarations':[d['name'] for d in declarations],
    'material_declarations':declarations,
    'source_files':list(sources.values()),
    'checked_bridge_modules':modules,
}
document = ['# Material imported definitions — development evidence\n',
            'Pinned source and excerpt hashes support provenance, not inventory completeness, mathematical fidelity or a build. Independent review and actual compilation are separate. The metric and pseudo-metric structures supply the distance used by the conclusions. This statement-driven inventory does not assert a complete transitive expansion of Lean core types such as Finite, Prod, Nat, or LE.\n']
for d in declarations:
    document.append(f"- `{d['name']}` ({d['role']}): {d['meaning']} Used by: " + ', '.join(f'`{n}`' for n in d['used_by']) + '.\n')
for src in sources.values():
    document.append(f"\n{src['url']}\nSHA256 `{src['sha256']}`\n\n```lean\n{src['upstream_header']}```\n")
    for e in src['excerpts']:
        document.append(f"\n{e['url']}\n```lean\n{e['text']}```\n")
(dest / 'verification').mkdir(exist_ok=True)
(dest / 'verification/material-imported-definitions.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n', encoding='utf-8', newline='\n')
(dest / 'MATERIAL-DEFINITIONS.md').write_text(''.join(document), encoding='utf-8', newline='\n')
print('declarations',len(declarations),'source files',len(sources),'excerpts',len(need))
