"""Retain exact pinned source evidence for the selected mathematical model.

This generator checks provenance; independent review establishes the scope and
interpretation, and separate Lean builds establish the semantic contracts.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = '56a005855ea17e0b0958f73ec801ae140b0a1679'
URL = 'https://github.com/leanprover-community/mathlib4'

# Each range includes its source-generating attributes and semantic context.
RANGES = {
 'measurable_space':('MeasureTheory/MeasurableSpace/Defs.lean',47,64),
 'generated_sigma':('MeasureTheory/MeasurableSpace/Defs.lean',319,335),
 'measurable':('MeasureTheory/MeasurableSpace/Defs.lean',489,493),
 'borel':('MeasureTheory/Constructions/BorelSpace/Basic.lean',49,52),
 'real_borel':('MeasureTheory/Constructions/BorelSpace/Basic.lean',711,717),
 'interval':('MeasureTheory/Integral/IntervalIntegral/Basic.lean',654,678),
 'bochner':('MeasureTheory/Integral/Bochner/Basic.lean',156,177),
 'bochner_contracts':('MeasureTheory/Integral/Bochner/Basic.lean',188,206),
 'integrable':('MeasureTheory/Function/L1Space/Integrable.lean',53,60),
 'restrict':('MeasureTheory/Measure/Restrict.lean',40,51),
 'restrict_contract':('MeasureTheory/Measure/Restrict.lean',71,76),
 'measure_space':('MeasureTheory/Measure/MeasureSpaceDef.lean',354,363),
 'real_measure':('MeasureTheory/Measure/Haar/OfBasis.lean',308,319),
 'lebesgue':('MeasureTheory/Measure/Lebesgue/Basic.lean',53,124),
 'set_intervals':('Order/Interval/Set/Defs.lean',61,82),
 'set_union':('Data/Set/Defs.lean',230,235),
 'set_image':('Data/Set/Defs.lean',260,264),
 'set_nonempty':('Data/Set/Defs.lean',275,280),
 'bounds':('Order/Bounds/Defs.lean',35,55),
 'real_extrema':('Algebra/Order/Archimedean/Real/Basic.lean',114,142),
 'nat_extrema':('Order/Lattice/Nat.lean',27,38),
 'nat_minimum':('Order/Lattice/Nat.lean',58,78),
 'finset':('Data/Finset/Defs.lean',72,79),
 'finite_product':('Data/Finset/Prod.lean',44,61),
 'finite_filter':('Data/Finset/Filter.lean',46,55),
 'finite_filter_membership':('Data/Finset/Filter.lean',122,133),
 'finite_card':('Data/Finset/Card.lean',44,55),
 'finite_fold':('Data/Finset/Fold.lean',30,43),
 'finite_sup':('Data/Finset/Lattice/Fold.lean',35,51),
 'disjoint':('Order/Disjoint.lean',35,49),
 'finite_disjoint':('Data/Finset/Disjoint.lean',44,51),
 'finite_union_instance':('Data/Finset/Lattice/Basic.lean',56,61),
 'finite_union_membership':('Data/Finset/Lattice/Basic.lean',98,104),
 'finite_intervals':('Order/Interval/Finset/Defs.lean',267,296),
 'integer_intervals':('Data/Int/Interval.lean',27,74),
 'filter':('Order/Filter/Defs.lean',69,82),
 'principal':('Order/Filter/Defs.lean',145,151),
 'eventually':('Order/Filter/Defs.lean',278,284),
 'filter_map':('Order/Filter/Defs.lean',411,417),
 'at_top':('Order/Filter/AtTopBot/Defs.lean',29,45),
 'tail':('Order/Filter/AtTopBot/Basic.lean',74,80),
 'limsup_generators':('Order/LiminfLimsup.lean',53,72),
 'limsup_contract':('Order/LiminfLimsup.lean',89,93),
}

def generate(package, dependency):
    def git(*args):
        return subprocess.check_output(['git','-C',str(dependency),*args])
    assert git('rev-parse','HEAD').decode().strip() == PIN
    config = json.loads((package/'comparator.json').read_text())
    assert config['definition_names'] == [], 'Fixed model definitions must not be definition holes'
    selected = config['theorem_names']
    fixed = json.loads((package/'verification/fixed-definitions.json').read_text())
    assert fixed['schema_version'] == 1
    fixed_names = fixed['fixed_definition_names']
    assert len(fixed_names) == len(set(fixed_names)) == 15
    prefix = 'ErdosOverlap.'
    # Edges expand the actual local statement/definition expressions. The finite
    # raw theorem spells its count and partition conditions inline, represented
    # here by their identical operator families, rather than a proof dependency.
    graph = {
      'Admissible':[], 'positiveOverlap':[], 'negativeOverlap':[],
      'overlapValues':['positiveOverlap','negativeOverlap'],
      'overlapPeak':['overlapValues'], 'relaxedPeaks':['Admissible','overlapPeak'],
      'relaxedOverlapConstant':['relaxedPeaks'], 'BinaryAdmissible':['Admissible'],
      'partitionPeaks':['BinaryAdmissible','overlapPeak'], 'erdosOverlapConstant':['partitionPeaks'],
      'Discrete.differenceCount':[], 'Discrete.maximumCount':['Discrete.differenceCount'],
      'Discrete.BalancedPartition':[], '_partition_formulation':[],
      'Discrete.finiteMaximumValues':['Discrete.BalancedPartition','Discrete.maximumCount'],
      'Discrete.minimumOverlap':['Discrete.finiteMaximumValues'],
      'Discrete.minimumOverlapQuotient':['Discrete.minimumOverlap'],
      'Discrete.discreteOverlapConstant':['Discrete.minimumOverlapQuotient'],
      'admissible_fields':['Admissible'],
      'Discrete.balancedPartition_fields':['Discrete.BalancedPartition'],
      'verified_peak_gt_auxiliary':['Admissible','overlapPeak'],
      'verified_auxiliary_le_relaxedOverlapConstant':['relaxedOverlapConstant'],
      'verified_auxiliary_le_erdosOverlapConstant':['erdosOverlapConstant'],
      'verified_auxiliary_le_discreteOverlapConstant':['Discrete.discreteOverlapConstant'],
      'verified_headline_lt_relaxedOverlapConstant':['relaxedOverlapConstant'],
      'verified_headline_lt_erdosOverlapConstant':['erdosOverlapConstant'],
      'verified_headline_lt_discreteOverlapConstant':['Discrete.discreteOverlapConstant'],
      'verified_auxiliary_lt_minimumOverlapQuotient':['Discrete.minimumOverlapQuotient'],
      'verified_finite_partition_difference':['Discrete.differenceCount','_partition_formulation'],
    }
    def closure(node):
        return {node}.union(*(closure(child) for child in graph[node]))
    assert all(name.removeprefix(prefix) in graph for name in selected)
    reached = set().union(*(closure(name.removeprefix(prefix)) for name in selected))
    assert all(name.removeprefix(prefix) in reached for name in fixed_names)
    def users(*roots):
        return [name for name in selected if closure(name.removeprefix(prefix)) & set(roots)]
    continuous = users('Admissible','positiveOverlap','negativeOverlap')
    integrals = continuous
    overlaps = users('Admissible','BinaryAdmissible','overlapValues')
    extrema = users('overlapPeak','relaxedOverlapConstant','erdosOverlapConstant',
                    'Discrete.discreteOverlapConstant')
    finite = users('Discrete.differenceCount','Discrete.BalancedPartition','_partition_formulation')
    partitions = users('Discrete.BalancedPartition','_partition_formulation')
    pairs = users('Discrete.differenceCount')
    maxima = users('Discrete.maximumCount')
    minima = users('Discrete.minimumOverlap')
    tails = users('Discrete.discreteOverlapConstant')
    declarations = []
    def add(name, kind, excerpt, meaning, uses, bridges=(), expansion='', bridge=None):
        assert set(uses) <= set(selected), name
        if bridge is None:
            bridge = ('class-fields' if kind in ['class','structure'] else
                      'proved-contract' if kind == 'theorem' else
                      'proved-equivalence' if kind == 'irreducible_def' else 'literal-unfolding')
        declarations.append(dict(name=name, declaration_kind=kind, role='definition', meaning=meaning,
            used_by=uses, definition_excerpt=excerpt, bridge_kind=bridge,
            bridge_excerpts=list(dict.fromkeys([excerpt,*bridges])),
            dependency_expansion=expansion or meaning,
            proof_status='Semantic contracts are exposed independently by SemanticChallenge and SemanticSolution; exact build outcomes are recorded in immutable verification receipts.'))

    add('MeasurableSpace','structure','measurable_space','A sigma-algebra is a predicate on sets, closed under empty set, complement and countable union.',continuous,['generated_sigma','borel','real_borel'])
    add('MeasurableSet','def','measurable_space','Membership in the ambient sigma-algebra; the real instance is Borel.',continuous,['real_borel'])
    add('MeasurableSpace.generateFrom','def','generated_sigma','The least sigma-algebra generated by the basic sets, using the retained GenerateMeasurable constructors.',continuous,['borel','real_borel'])
    add('Measurable','def','measurable','Every measurable target set has measurable preimage. Here both real sigma-algebras are Borel and measurability is global.',users('Admissible'),['measurable_space','borel','real_borel'])
    add('borel','def','borel','The sigma-algebra generated by all open sets of the canonical real topology.',continuous,['generated_sigma','real_borel'])
    add('Real.measurableSpace','instance','real_borel','The real measurable-space instance is borel Real, without completing the sigma-algebra.',continuous,['borel','generated_sigma'])
    add('intervalIntegral','def','interval','The oriented difference of restricted Bochner integrals over Ioc a b and Ioc b a. The unqualified notation uses volume.',integrals,['bochner','restrict','measure_space','real_measure','lebesgue'])
    add('MeasureTheory.integral','irreducible_def','bochner','The totalized Bochner integral; for integrable real-valued functions it is the L1 integral, and for nonintegrable functions it is zero.',integrals,['bochner_contracts'], expansion='CompleteSpace Real is canonical. The branch predicate Integrable includes a.e. strong measurability and finite norm integral. Physical integrability is proved in Overlap/KernelIntegrability and the actual leaf assembly; the semantic bridge retains the Integrable hypothesis of integral_eq and the negated hypothesis of integral_undef.')
    add('MeasureTheory.Integrable','def','integrable','The branch predicate is exactly a.e. strong measurability together with finite integral of the norm.',integrals,['bochner','bochner_contracts'])
    add('MeasureTheory.Measure.restrict','def','restrict','For a measurable test set t, restriction to s has measure mu(t intersection s). The test-set measurability hypothesis is retained.',integrals,['restrict_contract','interval','bochner'],bridge='proved-equivalence')
    add('MeasureTheory.MeasureSpace','class','measure_space','A measurable space with its default measure volume. No probability normalization is introduced.',integrals,['real_measure','lebesgue'])
    add('Real.measureSpace','instance','real_measure','The canonical real volume is the normalized additive Haar measure and agrees with Lebesgue length.',integrals,['measure_space','lebesgue'],bridge='proved-equivalence')
    add('Real.volume_eq_stieltjes_id','theorem','lebesgue','Real volume agrees with the identity Stieltjes measure; Ioc intervals have ofReal(b-a) volume and singletons are null.',integrals,['real_measure','interval'])
    add('Set.Icc','def','set_intervals','Closed real intervals contain exactly a <= x and x <= b.',overlaps)
    add('Set.Ioc','def','set_intervals','Left-open right-closed intervals contain exactly a < x and x <= b; conversion to Icc for integration uses null endpoints.',integrals,['lebesgue'])
    add('Set.image','def','set_image','Membership means there exists an input in the set whose image equals the target; overlapValues includes both signed branches.',users('overlapValues'),['set_union'])
    add('Set.union','def','set_union','Set union is disjunction of membership in either branch.',users('overlapValues'))
    add('Set.Nonempty','def','set_nonempty','There exists a member. Nonempty/bounded conditions are retained explicitly in real extrema contracts; the natural minimum also has a nonempty branch.',list(dict.fromkeys(extrema+minima)),['real_extrema','bounds','nat_extrema'])
    add('upperBounds','def','bounds','Upper bounds dominate every member. The retained to_dual attributes generate lowerBounds with the reversed inequality.',extrema,['real_extrema'])
    add('BddAbove','def','bounds','There exists an upper bound; the generated BddBelow is its order dual.',extrema,['set_nonempty','real_extrema'])
    add('IsLUB','def','bounds','A least upper bound is the least member of upperBounds; IsGLB is its generated dual.',extrema,['real_extrema'])
    add('Real.sSup_def','theorem','real_extrema','The real supremum chooses a LUB for nonempty bounded-above sets and returns zero otherwise. It is not an attained maximum.',extrema,['bounds','set_nonempty'], expansion='Anonymous SupSet Real instance and its named sSup_def/isLUB_sSup contracts are retained together. Real infimum also delegates to this supremum on the negated set. Constant.lean proves overlapValues_nonempty/bddAbove for admissible densities. The independent bridge keeps both assumptions.')
    add('Real.sInf_def','theorem','real_extrema','Real infimum is minus the supremum of the negated set, with GLB meaning for nonempty bounded-below sets.',users('relaxedOverlapConstant','erdosOverlapConstant'),['bounds','set_nonempty'], expansion='Anonymous InfSet Real and named sInf_def/isGLB_sInf contracts are retained. Constant.lean proves nonempty and bounded-below relaxedPeaks/partitionPeaks. Strict individual peaks give a non-strict infimum bound; the strictly smaller headline follows from the explicit rational gap.')
    add('Nat.sInf_def','theorem','nat_extrema','Natural infimum is Nat.find for a nonempty set and zero for an empty set. The minimum is attained under nonemptiness.',minima,['nat_minimum'], expansion='The anonymous InfSet Nat instance is distinct from real InfSet. DiscreteProblem proves finiteMaximumValues_nonempty and minimumOverlap_attained, including N=0. Numerical strict finite conclusions require N>0; real division at N=0 is total and zero.')
    add('Finset','structure','finset','A finite set is an underlying multiset without duplicate elements. Ordered pairs are counted once.',finite,['finite_product','finite_filter','finite_card'])
    add('Finset.product','def','finite_product','The Cartesian product contains ordered pairs whose two components belong to the corresponding finite sets.',pairs,['finset'])
    add('Finset.filter','def','finite_filter','A finite subset selected by a decidable predicate; the chosen predicate is the signed integer difference equality.',pairs,['finite_filter_membership','finite_product'])
    add('Finset.card','def','finite_card','The number of elements of the duplicate-free underlying multiset.',finite,['finset','finite_product','finite_filter'])
    add('Finset.fold','def','finite_fold','A commutative associative fold over the image, starting with the explicit base element.',maxima,['finite_sup'])
    add('Finset.sup','def','finite_sup','A fold of Nat max with bottom zero. It equals zero for an empty index set; it is not the nonempty sup-prime operator.',maxima,['finite_fold'], expansion='maximumCount indexes realized ordered differences. DiscreteCorrelation proves differenceCount_le_maximumCount for every integer, including unrealized differences, and attainment for nonempty A and B; DiscreteProblem gives the all-integer supremum interpretation.')
    add('Disjoint','def','disjoint','Every common lower bound lies below bottom; for finite sets the named membership contract means no common element.',partitions,['finite_disjoint'])
    add('Finset.disjoint_left','theorem','finite_disjoint','Finite-set disjointness is exactly that a member of the left set is not in the right set.',partitions,['disjoint'])
    add('Finset.mem_union','theorem','finite_union_membership','The anonymous finite-set Union instance has membership disjunction, with duplicates removed.',partitions,['finite_union_instance','finset'])
    add('Finset.Icc','def','finite_intervals','The finite closed interval supplied by LocallyFiniteOrder, including both integer endpoints.',partitions,['integer_intervals'])
    add('Int.instLocallyFiniteOrder','instance','integer_intervals','The integer finite intervals are built from a shifted natural range with toNat length and proved endpoint membership.',partitions,['finite_intervals'],bridge='proved-equivalence')
    add('Filter','structure','filter','A filter contains univ, is upward closed and closed under intersections; the structure itself permits the trivial filter.',tails,['principal','at_top','tail'])
    add('Filter.Eventually','def','eventually','The set on which the property holds belongs to the filter. At Nat.atTop this is a sufficiently large tail.',tails,['at_top','tail'])
    add('Filter.principal','def','principal','The filter of all supersets of the specified set.',tails,['filter','at_top'])
    add('Filter.map','def','filter_map','The forward filter: target sets belong when their preimages belong to the original filter.',tails,['eventually','limsup_generators'])
    add('Filter.atTop','def','at_top','The intersection of principal upper-tail filters; eventual membership on Nat is an existential tail threshold.',tails,['principal','tail'])
    for name in ['Filter.limsSup','Filter.limsup']:
        add(name,'def','limsup_generators','The retained literal limsup-side source generates limsInf/liminf by to_dual. The actual real liminf is the supremum of eventual lower bounds.',tails,['limsup_contract','filter_map','eventually','at_top','tail','real_extrema'], expansion='No literal def liminf source is fabricated: to_dual on limsSup/limsup/limsup_eq generates the actual selected operator. Both independent bridge modules prove Filter.liminf u Nat.atTop = sSup {a | exists N, forall n>=N, a<=u n}. This is a definition contract, not a convergence assertion. DiscreteProblem proves the quotient lies in [0,1] and supplies proper tail/cobounded hypotheses for the lower-bound transfer.',bridge='proved-equivalence')

    output = package/'verification'
    output.mkdir(exist_ok=True)
    source_files, texts = [], {}
    for stem, first, last in RANGES.values():
        path = 'Mathlib/'+stem
        if path not in texts:
            original = git('show',PIN+':'+path)
            assert (dependency/path).read_bytes() == original
            assert not git('status','--porcelain','--',path).strip()
            texts[path] = original
            header = original[:original.index(b'-/')+2].decode()+'\n'
            assert header.startswith('/-\n') and 'Copyright' in header and 'Apache 2.0' in header
            source_files.append(dict(path=path,url=f'{URL}/blob/{PIN}/{path}',
                sha256=hashlib.sha256(original).hexdigest(),
                git_blob_sha1=hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest(),
                license='Apache-2.0',upstream_header=header,excerpts=[]))
    by_path = {x['path']:x for x in source_files}
    for key,(stem,first,last) in RANGES.items():
        path = 'Mathlib/'+stem
        text = b''.join(texts[path].splitlines(keepends=True)[first-1:last]).decode()
        by_path[path]['excerpts'].append(dict(name=key,first_line=first,last_line=last,text=text,
            sha256=hashlib.sha256(text.encode()).hexdigest(),url=f'{URL}/blob/{PIN}/{path}#L{first}-L{last}'))
    modules = [dict(module='Semantic'+surface,path='Semantic'+surface+'.lean',
                    sha256=hashlib.sha256((package/('Semantic'+surface+'.lean')).read_bytes()).hexdigest())
               for surface in ['Challenge','Solution']]
    data = dict(schema_version=2,dependency=dict(name='mathlib',repository=URL,commit=PIN,
        lean_toolchain=(package/'lean-toolchain').read_text().strip()),
        documentation='verification/MATERIAL-IMPORTED-DEFINITIONS.md',
        required_declarations=[x['name'] for x in declarations],material_declarations=declarations,
        source_files=source_files,checked_bridge_modules=modules)
    doc = '''# Material imported definitions

This inventory retains the exact pinned model choices and their dependency
expansions. Source hashes and excerpt consistency are machine checked;
completeness and mathematical interpretation have independent review. The two
semantic modules import Challenge and Solution separately. Their compiled
contracts and exact-source outcomes belong to the release receipts.

The foundational boundary consists of logical connectives, quantifiers,
equality, function application, pairs, ordinary natural/integer/real arithmetic
and their canonical coercions. Model choices such as Borel sigma-algebras,
default volume, conditional real extrema, natural minima, finite-set union and
tail filters are retained explicitly below. Quotients at N=0 use total real
division; strict numerical finite statements require N>0. No discrete limit
existence or equality of continuous and discrete optimization problems is used.

Upstream Mathlib excerpts remain under Apache-2.0, with original attribution
and immutable URLs below. The project's own code and prose retain BSD-3-Clause.

## Selected surface

'''
    doc += '\n'.join('- `'+x+'`' for x in selected)+'\n\n'
    doc += ('The Comparator declares no definition holes. The following fixed model\n'
            'definitions are reached from the selected statement types and compared\n'
            'as full dependencies, including values. `AuditFixedDefinitions.lean`\n'
            'checks reachability in the actual elaborated environment, independently\n'
            'of the documentation graph used by this inventory generator.\n\n')
    doc += '\n'.join('- `'+x+'`' for x in fixed_names)+'\n\n## Meanings and contracts\n\n'
    for d in declarations:
        doc += f'### {d["name"]}\n\n{d["meaning"]}\n\n{d["dependency_expansion"]}\n\n'
        doc += 'Selected uses: '+', '.join('`'+x+'`' for x in d['used_by'])+'.\n\n'
        doc += d['proof_status']+'\n\n'
    doc += '## Exact upstream evidence\n\n'
    for s in source_files:
        doc += f'### {s["path"]}\n\n[{s["path"]}]({s["url"]})\n\nSHA-256: `{s["sha256"]}`. Git blob: `{s["git_blob_sha1"]}`.\n\n'
        doc += '```lean\n'+s['upstream_header']+'```\n\n'
        for e in s['excerpts']:
            doc += f'[{e["name"]}]({e["url"]}), lines {e["first_line"]}–{e["last_line"]}; SHA-256 `{e["sha256"]}`.\n\n'
            doc += '```lean\n'+e['text']+'```\n\n'
    (output/'material-imported-definitions.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
    (output/'MATERIAL-IMPORTED-DEFINITIONS.md').write_text(doc)
    print(json.dumps({'material_declarations':len(declarations),'source_files':len(source_files),
                      'excerpts':len(RANGES),'bridge_modules':[x['module'] for x in modules]}))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--dependency-root',type=Path)
    a = p.parse_args()
    generate(a.package,a.dependency_root or a.package/'.lake/packages/mathlib')
