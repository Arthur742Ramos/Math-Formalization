# Material imported definitions

This inventory covers the mathematical predicates and constructions materially used by the selected Comparator surface, including the definitions expanded by its local aliases. It retains exact pinned mathlib bytes and explains their semantics. It is an internal AI-authored source-fidelity audit; independent completeness/meaning review and its explicit expansion boundaries are documented in the separate review receipts. The consistency validator authenticates bytes, ranges, roles and selected-name coverage; it does not prove mathematical fidelity or compile Lean.

The separate bridge modules import Challenge and HodgeSolution respectively. Their assertions use actual operator fields, literal kernel/image/inverse-image membership, quotient descent and the canonical proved abstract-homology/quotient isomorphism. Successful compilation must be reported separately against final source bytes; this document does not claim a protected Comparator or registry check.

Scope and explicit exclusions: foundational Lean logic (equality, quantifiers, conjunction, implication, existential witnesses, Nonempty, Subtype, Quotient), integer arithmetic and pairs, function composition/coercion, and generic order/set infrastructure (membership, subset order, Antitone, intersection/infimum, supremum/sum, indexed suprema/infima, top and bottom) are not separately inventoried. Their uses are ordinary: inf is intersection, sup is submodule sum, indexed sup is span of the union, top is the whole module and bottom is zero. Subsingleton in support hypotheses means every two vectors coincide, hence each supported-outside object is zero; there is no dimension convention. Standard inherited algebra infrastructure (CommRing, DivisionRing, AddCommGroup, DistribMulAction, AddHom, MulActionHom), generic categorical infrastructure (Category, composition, identity, functor, cone/cocone, kernel fork and cokernel cofork), and their typeclass-instance plumbing are expansion boundaries rather than omitted Hodge hypotheses. The retained Field, Module, ModuleCat, LinearMap, Submodule, IsLimit and IsColimit definitions state the relevant contracts. We do not inventory every transitive theorem or tactic dependency.

HomologicalComplex₂, CochainComplex, ModuleCat.of, ModuleCat.Hom.hom, HomologicalComplex.sc/sc' and CohomologicalSpectralSequence are upstream abbreviations; their underlying material structures/definitions and relevant alias excerpts are retained below. Local Page, InfinityPage and GradedCohomology are actual submodule quotients, with denominator pulled back to the numerator along its subtype. The quotient relation is proved equivalent to difference-membership; the abstract homology object is canonically isomorphic to its kernel/image quotient, not definitionally equal to it.

The square convention is commuting in the underlying bicomplex. The genuine total differential supplies the vertical (-1)^p sign. The selected surface does not assert categorical reconstruction of arbitrary anticommuting bicomplexes, analytic Kähler hypotheses, or a second filtration. Spectral sequences start at 1 with differential bidegree (r,1-r); actual quotient representatives and canonical homology projection certify their recurrence. Bounded abutment is the associated graded of the actual induced filtration on total cohomology.

## Selected surface

- `AlgebraicHodgePilot.exists_closed_representative`
- `AlgebraicHodgePilot.Column.all_differentials_zero`
- `AlgebraicHodgePilot.Column.associatedSequence_transition_next`
- `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`
- `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`
- `AlgebraicHodgePilot.Column.bounded_e1_degeneration`
- `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`
- `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`
- `AlgebraicHodgePilot.ImageKernel`
- `AlgebraicHodgePilot.Column.RectangularSupport`
- `AlgebraicHodgePilot.Column.HorizontalSupport`
- `AlgebraicHodgePilot.Column.filtration`
- `AlgebraicHodgePilot.Filtered.cycles`
- `AlgebraicHodgePilot.Filtered.boundaries`
- `AlgebraicHodgePilot.Filtered.denominator`
- `AlgebraicHodgePilot.Filtered.Page`
- `AlgebraicHodgePilot.Filtered.closedCycles`
- `AlgebraicHodgePilot.Filtered.closedBoundaries`
- `AlgebraicHodgePilot.Filtered.closedDenominator`
- `AlgebraicHodgePilot.Filtered.InfinityPage`
- `AlgebraicHodgePilot.Filtered.cohomologyFiltration`
- `AlgebraicHodgePilot.Filtered.GradedCohomology`
- `AlgebraicHodgePilot.Column.firstPageIso`
- `AlgebraicHodgePilot.Column.associatedSequence`
- `AlgebraicHodgePilot.Column.boundedStableGradedIso`

## Declaration meanings and dependency expansion

### `Field`

Role: hypothesis; kind: class; bridge: class-fields.

A commutative field, including the inherited division-ring nontriviality and zero-inverse convention.

Field k is inherited throughout. Fixed coefficient universe Type; integer indices. No characteristic-zero, finite-dimensional or analytic hypothesis is implicit. Its CommRing and DivisionRing parents are standard algebra infrastructure, not extra Hodge assumptions.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Module`

Role: definition; kind: class; bridge: class-fields.

Scalar action distributes and obeys module laws. Over Field k the objects are vector spaces.

Extends DistribMulAction; inherited scalar associativity, identity and zero, plus add_smul and zero_smul. AddCommGroup is carried by ModuleCat.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ModuleCat`

Role: definition; kind: structure; bridge: class-fields.

Bundled additive commutative groups with k-module structure.

carrier is Type v; isAddCommGroup and isModule are fields. of is an abbreviation building this structure; no dimensions or equality-only replacement.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ModuleCat.Hom`

Role: definition; kind: structure; bridge: class-fields.

Category morphisms are bundled actual linear maps.

Hom.hom and ofHom are abbreviations to ConcreteCategory structure; moduleCategory composition is g.comp f, identity is LinearMap.id.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearMap`

Role: definition; kind: structure; bridge: class-fields.

Actual additive scalar-compatible maps, with ordinary linear maps using RingHom.id.

Extends AddHom and MulActionHom; function coercion is the underlying map. The tests check add/scalar preservation.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule`

Role: definition; kind: structure; bridge: class-fields.

Actual subsets closed under addition and scalar multiplication.

Extends AddSubmonoid and SubMulAction. SetLike gives membership; PartialOrder is subset inclusion. Intersection, sum, indexed sum, top and bottom use the inherited complete lattice, not numeric proxies.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearMap.ker`

Role: definition; kind: def; bridge: literal-unfolding.

Vectors mapped to zero.

ker f is comap f bottom; bottom membership is equality to zero. Tests prove membership by literal unfolding.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearMap.range`

Role: definition; kind: def; bridge: literal-unfolding.

Vectors with an actual preimage under a linear map.

map f top is copied to Set.range f. RingHomSurjective for ordinary linear maps is identity-surjectivity; no extra field assumption.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.map`

Role: definition; kind: def; bridge: literal-unfolding.

Actual image of the submodule under a linear map.

Carrier is f image p, witnessed by x∈p with f x=y. Ordinary linear maps specialize the semilinear interface.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.comap`

Role: definition; kind: def; bridge: literal-unfolding.

Actual inverse image of a submodule.

Carrier is f preimage p. Quotient denominators are pulled back along the inclusion of the numerator submodule.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.quotientRel`

Role: definition; kind: def; bridge: proved-equivalence.

Submodule quotient identifies elements whose difference lies in the submodule.

Literal relation is QuotientAddGroup.leftRel (-x+y∈p); quotientRel_def proves the x-y form, NOT a definitional equality.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.Quotient.mk`

Role: definition; kind: def; bridge: literal-unfolding.

Class of an actual vector in the quotient.

HasQuotient above uses Lean Quotient of quotientRel. Quotient.mk is Quotient.mk double-prime; foundational quotient is an explicit exclusion.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.mkQ`

Role: definition; kind: def; bridge: proved-equivalence.

Linear quotient-class projection.

toFun is Quotient.mk; zero iff denominator membership is a PROVED upstream theorem used in both tests.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Submodule.liftQ`

Role: definition; kind: def; bridge: literal-unfolding.

Linear descent of a map vanishing on the denominator.

Input h:p≤ker f is an actual well-definedness proof. It uses quotient-group descent and scalar compatibility; lift applied to mkQ is literal f.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ComplexShape`

Role: definition; kind: structure; bridge: class-fields.

Allowed differential incidence relation, with unique next and previous incidence.

Coherent incidence relation, not an operator. Complex operators and square-zero are separate HomologicalComplex fields.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ComplexShape.up'`

Role: definition; kind: def; bridge: literal-unfolding.

Differentials with index increment a.

Rel i j is i+a=j. Used with a=1 for total/columns and a=(r,1-r) for conventional spectral pages.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ComplexShape.up`

Role: definition; kind: def; bridge: literal-unfolding.

Cochain shape with increment one.

Abbreviation-like definition up alpha := up' 1; the upstream declaration is a def. Integer indices are not replacing actual operators.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex`

Role: hypothesis-and-conclusion; kind: structure; bridge: class-fields.

Objects and actual differential morphisms, zero off shape, with d composed d zero.

CochainComplex is an abbreviation to this structure with up. HomologicalComplex₂ abbreviates this structure nested in itself; morphisms in the outer complex enforce commuting squares. No homology or degeneration fields.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.ImageKernel`, `AlgebraicHodgePilot.Column.RectangularSupport`, `AlgebraicHodgePilot.Column.HorizontalSupport`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Filtered.cycles`, `AlgebraicHodgePilot.Filtered.boundaries`, `AlgebraicHodgePilot.Filtered.denominator`, `AlgebraicHodgePilot.Filtered.Page`, `AlgebraicHodgePilot.Filtered.closedCycles`, `AlgebraicHodgePilot.Filtered.closedBoundaries`, `AlgebraicHodgePilot.Filtered.closedDenominator`, `AlgebraicHodgePilot.Filtered.InfinityPage`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.Iso`

Role: conclusion; kind: structure; bridge: class-fields.

Actual morphism with inverse and both inverse laws.

In ModuleCat both maps are actual linear maps. Isomorphism symbols in E1 and stable-grading comparisons denote this structure, never equality of dimensions.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.SpectralSequence`

Role: conclusion; kind: structure; bridge: class-fields.

Page complexes and actual homology-to-next-page isomorphisms from a stated first index.

CohomologicalSpectralSequence is an abbreviation with shapes up'(r,1-r); starting index is 1. Common-representative and all-next-class transition theorems further certify association beyond these fields.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.associatedSequence`.

### `CategoryTheory.ShortComplex`

Role: definition; kind: structure; bridge: class-fields.

Two composable actual maps with zero composition.

Three objects, f, g and f≫g=0. A column or page short complex is obtained from actual HomologicalComplex.d.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.LeftHomologyData`

Role: definition; kind: structure; bridge: class-fields.

Kernel of outgoing map, then cokernel of incoming map restricted to cycles.

wi, hi, wπ, hπ require actual universal properties IsLimit and IsColimit; quotient interpretation is established by moduleCatLeftHomologyData.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.Limits.IsLimit`

Role: definition; kind: structure; bridge: class-fields.

Universal limit cone, including factorization and uniqueness.

For a KernelFork this says the inclusion represents the kernel, not merely square-zero. Cone and categorical composition infrastructure are excluded as generic foundations.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.Limits.IsColimit`

Role: definition; kind: structure; bridge: class-fields.

Universal colimit cocone, including factorization and uniqueness.

For a CokernelCofork this says projection represents the cokernel. Cocone and categorical composition infrastructure are generic foundations.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.HomologyData`

Role: definition; kind: structure; bridge: class-fields.

Compatible left and right homology data.

The chosen left.H is the actual homology object; compatibility iso and comm make the two dual constructions agree. RightHomologyData is dual to the retained LeftHomologyData and is retained separately, not a new Hodge assumption.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.HasHomology`

Role: definition; kind: class; bridge: class-fields.

Existence of actual homology data.

condition is Nonempty HomologyData. In ModuleCat this is supplied by its abelian structure; no arbitrary page computation is supplied.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.homologyData`

Role: definition; kind: def; bridge: literal-unfolding.

Chosen actual homology data from its existence.

Uses Classical.choice via Nonempty.some. This is standard axiom use recorded in audit, not a new mathematical axiom.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.homology`

Role: definition; kind: def; bridge: proved-equivalence.

Left.H of the chosen compatible homology data.

Abstract categorical homology is not literally the quotient type; moduleCatHomologyIso is the PROVED canonical bridge.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex.shortComplexFunctor'`

Role: definition; kind: def; bridge: literal-unfolding.

Actual incoming and outgoing differentials form a short complex.

sc' is obj of this functor. sc uses shape.prev/next. The d_comp_d law supplies the zero composite.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex.homology`

Role: definition; kind: def; bridge: proved-equivalence.

Homology of the short complex at the requested degree.

sc uses actual predecessor and successor differentials. homologyIsoSc' identifies explicit integer predecessor/successor with that API.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex.homologyIsoSc'`

Role: definition; kind: def; bridge: proved-equivalence.

Canonical homology comparison for explicit predecessor and successor indices.

Built from the actual short-complex isomorphism by homologyMapIso; requires equalities of shape.prev/next. Not definitional equality.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.moduleCatLeftHomologyData`

Role: definition; kind: def; bridge: literal-unfolding.

Concrete cycles ker g and quotient by incoming range.

moduleCatToCycles is f restricted to ker g using zero composite. H is quotient of ker g by range of that restriction, π is actual mkQ; universal properties prove valid categorical homology data.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.moduleCatHomologyIso`

Role: definition; kind: def; bridge: proved-equivalence.

Canonical abstract-homology to concrete kernel/image quotient isomorphism.

Uses moduleCatLeftHomologyData.homologyIso. Projection compatibility is a theorem; quotient representation is not asserted as definitional equality.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.LeftHomologyData.ofZeros`

Role: definition; kind: def; bridge: literal-unfolding.

Canonical homology data when both actual adjacent maps vanish.

K=H=middle object; i=π=identity, with proved kernel/cokernel universality. Used only after actual page differentials have been proved zero.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.associatedSequence`.

### `HomologicalComplex₂.total`

Role: definition; kind: def; bridge: literal-unfolding.

Actual signed total complex of a commuting bicomplex.

Objects are categorical coproducts along p+q=n via GradedObject.mapObj. Differential is D₁+D₂ induced from actual horizontal/vertical maps, with signs. Full component formula is proved locally. Totalization requires HasTotal, an alias of GradedObject.HasMap, meaning coproducts over each degree fiber. Here ModuleCat has the required small colimits by its proved colimit instances; these are synthesized from the fixed category, not an additional bicomplex or Hodge hypothesis.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex₂.ιTotal`

Role: definition; kind: def; bridge: literal-unfolding.

Actual coproduct inclusion of each bidegree summand in the total complex.

Uses GradedObject.ιMapObj; column filtration is indexed supremum of actual ranges of these maps, p≤a and a+b=n. Totalization requires HasTotal, an alias of GradedObject.HasMap, meaning coproducts over each degree fiber. Here ModuleCat has the required small colimits by its proved colimit instances; these are synthesized from the fixed category, not an additional bicomplex or Hodge hypothesis.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.GradedObject.mapObj`

Role: definition; kind: def; bridge: literal-unfolding.

Coproduct of graded components over each fiber of an index map.

π maps (p,q) to p+q in the up/up/up total shape; actual categorical coproducts exist in ModuleCat. This is direct sum totalization, not an unrestricted product. Totalization requires HasTotal, an alias of GradedObject.HasMap, meaning coproducts over each degree fiber. Here ModuleCat has the required small colimits by its proved colimit instances; these are synthesized from the fixed category, not an additional bicomplex or Hodge hypothesis.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex₂.d₁`

Role: proof-dependency; kind: def; bridge: literal-unfolding.

Horizontal total differential on a summand with totalization sign.

Uses ε₁ and outer K.d followed by actual summand inclusion; up/up convention makes horizontal sign 1. Totalization requires HasTotal, an alias of GradedObject.HasMap, meaning coproducts over each degree fiber. Here ModuleCat has the required small colimits by its proved colimit instances; these are synthesized from the fixed category, not an additional bicomplex or Hodge hypothesis.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `HomologicalComplex₂.d₂`

Role: proof-dependency; kind: def; bridge: literal-unfolding.

Vertical total differential on a summand with totalization sign.

Uses ε₂ and inner differential followed by actual summand inclusion; up/up convention gives (-1)^p. Signs follow ComplexShapeSigns instances; local full component theorem checks actual totalization. Totalization requires HasTotal, an alias of GradedObject.HasMap, meaning coproducts over each degree fiber. Here ModuleCat has the required small colimits by its proved colimit instances; these are synthesized from the fixed category, not an additional bicomplex or Hodge hypothesis.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.RightHomologyData`

Role: definition; kind: structure; bridge: class-fields.

Dual cokernel-then-kernel homology data, compatible with left homology.

Q is cokernel of f and H is kernel of induced g; hp and hι are actual universal properties. No Hodge assumption is present.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `CategoryTheory.ShortComplex.LeftHomologyData.homologyIso`

Role: definition; kind: def; bridge: proved-equivalence.

Canonical isomorphism from chosen abstract homology to any proved left homology data.

Composes the inverse leftHomologyIso with the unique comparison for the supplied left data. Its π-compatibility is a theorem, retained separately.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Filtered.cohomologyFiltration`, `AlgebraicHodgePilot.Filtered.GradedCohomology`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `TotalComplexShape`

Role: proof-dependency; kind: class; bridge: class-fields.

Index and horizontal/vertical signs making signed totalization square to zero.

The up/up/up instance uses π(p,q)=p+q, horizontal ε₁=1 and vertical ε₂=(-1)^p. No supplied degeneration statement is in this class.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `ComplexShape.TensorSigns`

Role: proof-dependency; kind: class; bridge: class-fields.

Sign homomorphism and compatibility of an additive complex shape.

The up integer instance is Int.negOnePow; ε changes sign along a permitted differential.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `Int.negOnePow`

Role: proof-dependency; kind: def; bridge: literal-unfolding.

The genuine sign (-1)^n as an integer unit.

Integer-unit action on module morphisms is the usual sign; this is a sign coefficient on actual operators, not arithmetic substituted for an operator.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.filtration`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearEquiv`

Role: proof-dependency; kind: structure; bridge: class-fields.

An invertible actual linear map with an actual inverse function.

Extends LinearMap and additive equivalence; inverse laws are inherited from the equivalence. This is used to construct, not assume, the selected comparison isomorphisms.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearEquiv.ofBijective`

Role: proof-dependency; kind: def; bridge: literal-unfolding.

Converts a proved bijective linear map into an actual inverse-bearing linear equivalence.

Composes the equivalence onto its range from proved injectivity with the equivalence from proved range=top from surjectivity. The inverse uses standard classical choice, audited separately.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

### `LinearEquiv.toModuleIso`

Role: proof-dependency; kind: def; bridge: literal-unfolding.

Turns actual linear equivalence into actual categorical module isomorphism.

hom is the original linear map and inv is its symmetric linear map; both inverse identities are proved from the equivalence.

Separate HodgeChallengeTests and HodgeSolutionTests assert literal membership, operator, quotient and field contracts; exact entrypoint compilation is recorded separately. Retained upstream bridge excerpts establish definitions; no hash check is represented as a proof.

Used by: `AlgebraicHodgePilot.exists_closed_representative`, `AlgebraicHodgePilot.Column.all_differentials_zero`, `AlgebraicHodgePilot.Column.associatedSequence_transition_next`, `AlgebraicHodgePilot.Column.associatedSequence_transition_covers`, `AlgebraicHodgePilot.Column.cohomologyFiltration_exhaustive_separated`, `AlgebraicHodgePilot.Column.bounded_e1_degeneration`, `AlgebraicHodgePilot.Column.boundedStableGradedIso_closed`, `AlgebraicHodgePilot.Column.zeroPageHomologyIso_π`, `AlgebraicHodgePilot.Column.firstPageIso`, `AlgebraicHodgePilot.Column.associatedSequence`, `AlgebraicHodgePilot.Column.boundedStableGradedIso`.

## Immutable source and excerpt evidence

Every excerpt below is reproduced literally, including comments and nearby context. Attribution belongs to the retained upstream header; local bridges and inventory prose are AI-assisted project contributions. Full-file hashes authenticate the file, while excerpt hashes authenticate these exact ranges.

### `Mathlib/Algebra/Field/Defs.lean`

[Mathlib/Algebra/Field/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean)

Full SHA256: `341e5bbbc77690b9cce20dd460d0a4c22138beea4ed9e10cc100c4d4a2db6152`. Git blob SHA1: `c7cfb7246b4896ec3fc910efbfdeb50261baddeb`. License: Apache-2.0.

```lean
/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
```

`Field` — [lines 169–180](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean#L169-L180); SHA256 `175f1b3382fe443c80704d1eef6aee380a13f418aa87db21e390e449d182d5ae`.

```lean

/-- A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.

An instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.
Those two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need
to control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also note [forgetful inheritance].

If the field has positive characteristic `p`, our division by zero convention forces
`ratCast (1 / p) = 1 / 0 = 0`. -/
@[stacks 09FD "first part"]
class Field (K : Type u) extends CommRing K, DivisionRing K
```

### `Mathlib/Algebra/Module/Defs.lean`

[Mathlib/Algebra/Module/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Defs.lean)

Full SHA256: `e67222f427fb2b194a3407d42b9ca311fc87148b929e439ad1fa638dd3d365a8`. Git blob SHA1: `658209d4f26b59f63ef01b69125ce60e37906b51`. License: Apache-2.0.

```lean
/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
```

`Module` — [lines 47–60](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Defs.lean#L47-L60); SHA256 `ac3f28349bec43f4abd1b38d6f44bf14add1748df12a8cfe19d53af4a4953201`.

```lean

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

```

### `Mathlib/Algebra/Category/ModuleCat/Basic.lean`

[Mathlib/Algebra/Category/ModuleCat/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Basic.lean)

Full SHA256: `8623e6251cb6c74a669576f9ea364254be0b96bcc3114975bd76bc60f516a9ff`. Git blob SHA1: `f47526b890fd2cf85dd32a406366286f55413aa1`. License: Apache-2.0.

```lean
/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
```

`ModuleCat` — [lines 47–65](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Basic.lean#L47-L65); SHA256 `8428b659a522891f636b044dd66edfb1c7664a075d54d3d5469b4e985049f0a4`.

```lean

variable (R : Type u) [Ring R]

/-- The category of R-modules and their morphisms.

Note that in the case of `R = ℤ`, we cannot
impose here that the `ℤ`-multiplication field from the module structure is defeq to the one coming
from the `isAddCommGroup` structure (contrary to what we do for all module structures in
mathlib), which creates some difficulties down the road. -/
structure ModuleCat where
  _mkInternal ::
  /-- the underlying type of an object in `ModuleCat R` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]

initialize_simps_projections ModuleCat (-isModule, -isAddCommGroup)
attribute [instance] ModuleCat.isAddCommGroup
attribute [instance 1100] ModuleCat.isModule
```

`ModuleCat_Hom` — [lines 92–118](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Basic.lean#L92-L118); SHA256 `18d69f2136f7c305c819cd17e5e953b41a88b2b3cfe119f868bd9027fa562b6d`.

```lean
/-- The type of morphisms in `ModuleCat R`. -/
@[ext]
structure Hom (M N : ModuleCat.{v} R) where
  _mkInternal ::
  /-- The underlying linear map. -/
  hom' : M →ₗ[R] N

instance moduleCategory : Category.{v, max (v + 1) u} (ModuleCat.{v} R) where
  Hom M N := Hom M N
  id _ := ⟨LinearMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (ModuleCat.{v} R) (· →ₗ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom._mkInternal

section

variable {R}

/-- Turn a morphism in `ModuleCat` back into a `LinearMap`. -/
abbrev Hom.hom {A B : ModuleCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := ModuleCat R) f

/-- Typecheck a `LinearMap` as a morphism in `ModuleCat`. -/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
```

`LinearEquiv_toModuleIso` — [lines 272–280](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Basic.lean#L272-L280); SHA256 `d5ce41006b33c4b37a16316ec5dad83c3b557d04f9275321e0b030cfaa65415e`.

```lean
/-- Build an isomorphism in the category `Module R` from a `LinearEquiv` between `Module`s. -/
@[simps]
def LinearEquiv.toModuleIso {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : Module R X₁}
    {m₂ : Module R X₂} (e : X₁ ≃ₗ[R] X₂) : ModuleCat.of R X₁ ≅ ModuleCat.of R X₂ where
  hom := ofHom (e : X₁ →ₗ[R] X₂)
  inv := ofHom (e.symm : X₂ →ₗ[R] X₁)
  hom_inv_id := by ext; apply e.left_inv
  inv_hom_id := by ext; apply e.right_inv

```

`modulecat_of_alias` — [lines 76–82](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Basic.lean#L76-L82); SHA256 `dacead73f08b22dbfc6c4b75aca5cdf7f9293ecb65d855037c247f36d3409765`.

```lean
abbrev of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat.{v} R :=
  ⟨X⟩

open Lean.PrettyPrinter.Delaborator in
/-- This prints `ModuleCat.of R X` as `↧X`. -/
@[app_delab ModuleCat.of]
meta def delabOf : Delab := CategoryTheory.delabOf
```

### `Mathlib/Algebra/Module/LinearMap/Defs.lean`

[Mathlib/Algebra/Module/LinearMap/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean)

Full SHA256: `aea1c354ffc798aaa5397f2f58124bc2ed7b29d24227ae568d3f5745f839570d`. Git blob SHA1: `5f68ae60b4f22094ae57c9e4ef28be13925e8ef7`. License: Apache-2.0.

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
```

`LinearMap` — [lines 79–98](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean#L79-L98); SHA256 `2f918943b66eca53992f8d19fde14bdd74a20eb429e4474d5a2e9359478b80d7`.

```lean
/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. -/
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

/-- The `MulActionHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toMulActionHom

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom

/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
```

### `Mathlib/Algebra/Module/Submodule/Defs.lean`

[Mathlib/Algebra/Module/Submodule/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Defs.lean)

Full SHA256: `f1735fb71af000fc2047c5e6456fa2b31d0f5443d23a169ac25a6ce388fe2b78`. Git blob SHA1: `ceec21a0216a4bb5187d1f87c5a068caf26b7f62`. License: Apache-2.0.

```lean
/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
```

`Submodule` — [lines 37–60](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Defs.lean#L37-L60); SHA256 `e1855cee6bc91ba052f21bf09daa0cda5fddb919bbd4f7a963cdbda50c13fbf5`.

```lean

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance setLike : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance : PartialOrder (Submodule R M) := .ofSetLike (Submodule R M) M

initialize_simps_projections Submodule (carrier → coe, as_prefix coe)
```

### `Mathlib/Algebra/Module/Submodule/Ker.lean`

[Mathlib/Algebra/Module/Submodule/Ker.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Ker.lean)

Full SHA256: `6820cd12f24bc4d7b00c6e508c2d2ecaff39549d74be47430eb76cd8b6ee34ee`. Git blob SHA1: `c64fd7feb84fc02de4f53ec66b9bc0d7a30b1fa2`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

`LinearMap_ker` — [lines 57–66](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Ker.lean#L57-L66); SHA256 `f99d3c7cc74e3c5d16b8da2613084dec0781f45b988fc4e75f6a7cdafb92c692`.

```lean

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂

```

### `Mathlib/Algebra/Module/Submodule/Range.lean`

[Mathlib/Algebra/Module/Submodule/Range.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Range.lean)

Full SHA256: `5d3c93d9b771e9aec611a0221bc138f9491dd2c37c3babcf42c2acbe570a4d45`. Git blob SHA1: `5ea20b9bee1b24bbf5a32bedfa428bb1a84c129a`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

`LinearMap_range` — [lines 55–72](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Range.lean#L55-L72); SHA256 `adf5d395d52333f1b10152e8d261c332f795a411c61bda554f44e6a4eb447067`.

```lean
/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

theorem coe_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : (range f : Set M₂) = Set.range f :=
  rfl

theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl

@[simp]
theorem mem_range [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

theorem range_eq_map [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : range f = map f ⊤ := by
  ext
```

### `Mathlib/Algebra/Module/Submodule/Map.lean`

[Mathlib/Algebra/Module/Submodule/Map.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Map.lean)

Full SHA256: `f0b02929b7aeeb359f7c9f207a7d78d3013ecf9a5e2e167431cf85422894ebc2`. Git blob SHA1: `56d22fe8c8ac84bf173514e5283440e673e58b3d`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

`Submodule_map` — [lines 52–63](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Map.lean#L52-L63); SHA256 `43c7d9bf8328545441dd94462a3c9b822fa099a626bb091b158d37a2ba84eee7`.

```lean
/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]
theorem map_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl
```

`Submodule_comap` — [lines 170–180](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Map.lean#L170-L180); SHA256 `2fef0745a4245d0f10214979089d0ddabb74442edd3efc25e0afabeb14be3156`.

```lean
/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
@[implicit_reducible]
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]
theorem comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl
```

### `Mathlib/LinearAlgebra/Quotient/Defs.lean`

[Mathlib/LinearAlgebra/Quotient/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean)

Full SHA256: `ddb08efd66c7dd6f5e142ac3e1edc1189ea30de276f1e78f4193d6ee80676fb3`. Git blob SHA1: `2c25d9a529dfd044d3bf88361d79a3e8de23fda3`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

`Submodule_quotientRel` — [lines 39–57](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L39-L57); SHA256 `21dab74d3018467ac7bf1c170ab32ad7f59b7aeaba1a6388e0a8fdb042b6b67d`.

```lean

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be defeq to the `AddSubgroup`
version, where commutativity can't be assumed. -/
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [quotientRel, leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

```

`Submodule_Quotient_mk` — [lines 59–66](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L59-L66); SHA256 `d4de14806870c147d5222c268add70db6ac7e969607afdd4848ead39f5a21357`.

```lean
/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''

theorem mk'_eq_mk' {p : Submodule R M} (x : M) :
    @Quotient.mk' _ (quotientRel p) x = mk x :=
  rfl
```

`Submodule_mkQ` — [lines 226–240](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L226-L240); SHA256 `23f8e0b54dc6ef9e541e10165b88217d4a2e4e6a381f4af942ea23855386d0df`.

```lean
/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl

theorem mkQ_surjective : Function.Surjective p.mkQ := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

end

```

`quotient_class_equality` — [lines 77–98](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Defs.lean#L77-L98); SHA256 `16c7a00726cb442dd6d3c04079e507d5f48e2b48bea3bf4879d64ad81431b3e4`.

```lean

protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq

protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)

instance : Zero (M ⧸ p) where
  -- Use Quotient.mk'' instead of mk here because mk is not reducible.
  -- This would lead to non-defeq diamonds.
  -- See also the same comment at the One instance for Con.
  zero := Quotient.mk'' 0

instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

@[simp]
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl

@[simp]
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)
```

### `Mathlib/LinearAlgebra/Quotient/Basic.lean`

[Mathlib/LinearAlgebra/Quotient/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Basic.lean)

Full SHA256: `564aad5ee0111df700cb30aca030018f26939ed1c307f19ee6d9ac02b6bc4312`. Git blob SHA1: `4a0da4567b8b41ad8120b46809c6270e0a00bf14`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

`Submodule_liftQ` — [lines 116–127](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Quotient/Basic.lean#L116-L127); SHA256 `9479fb8d21fe62bcb065a5eedf0da28e6b95c1acd1e7fa58619c413f8383561e`.

```lean
/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by rintro a ⟨x⟩; exact f.map_smulₛₗ a x }

@[simp]
theorem liftQ_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftQ f h (Quotient.mk x) = f x :=
  rfl

@[simp]
theorem liftQ_mkQ (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).comp p.mkQ = f := by ext; rfl
```

### `Mathlib/Algebra/Homology/ComplexShape.lean`

[Mathlib/Algebra/Homology/ComplexShape.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShape.lean)

Full SHA256: `6cf9e3c6c08f348416581aae844c77d1feb8489f90fbffafc3f371612da69e78`. Git blob SHA1: `f28889b981c35b3c171eba6a92aa6603a5af8a70`. License: Apache-2.0.

```lean
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
```

`ComplexShape` — [lines 59–73](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShape.lean#L59-L73); SHA256 `3cc57e2a592201d3358a191488d05038334dc0b01bc4ed25f30a32149160340b`.

```lean

Below we define `c.next` and `c.prev` which provide these related elements.
-/
@[ext]
structure ComplexShape (ι : Type*) where
  /-- Nonzero differentials `X i ⟶ X j` shall be allowed
  on homological complexes when `Rel i j` holds. -/
  Rel : ι → ι → Prop
  /-- There is at most one nonzero differential from `X i`. -/
  next_eq : ∀ {i j j'}, Rel i j → Rel i j' → j = j'
  /-- There is at most one nonzero differential to `X j`. -/
  prev_eq : ∀ {i i' j}, Rel i j → Rel i' j → i = i'

attribute [to_dual self (reorder := 3 4)] ComplexShape.Rel
attribute [to_dual existing] ComplexShape.next_eq
```

`ComplexShape_up'` — [lines 160–168](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShape.lean#L160-L168); SHA256 `5136bdc9b1e457aac69789d369d59a59a067d0c570047dcce608c1f4481d5590`.

```lean

/-- The `ComplexShape` allowing differentials from `X i` to `X (i+a)`.
(For example when `a = 1`, a cohomology theory indexed by `ℕ` or `ℤ`)
-/
def up' {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) : ComplexShape α where
  Rel i j := i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)

```

`ComplexShape_up` — [lines 181–188](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShape.lean#L181-L188); SHA256 `e46660afa3e85d78178fa275d39b4514c7f28eaa50110a5b652b3eac5e823b22`.

```lean

/-- The `ComplexShape` appropriate for cohomology, so `d : X i ⟶ X j` only when `j = i + 1`.
-/
@[to_dual (attr := simps!) down
/-- The `ComplexShape` appropriate for homology, so `d : X i ⟶ X j` only when `i = j + 1`.
-/]
def up (α : Type*) [Add α] [IsRightCancelAdd α] [One α] : ComplexShape α :=
  up' 1
```

### `Mathlib/Algebra/Homology/HomologicalComplex.lean`

[Mathlib/Algebra/Homology/HomologicalComplex.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalComplex.lean)

Full SHA256: `a4857ea05154321bfeb2fa8e906ad87e24977a49cd03cb8785f3f9b19ffa42df`. Git blob SHA1: `50646b814429df3f77ee4be826053853b54d6c64`. License: Apache-2.0.

```lean
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
```

`HomologicalComplex` — [lines 49–79](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalComplex.lean#L49-L79); SHA256 `3abeb4af81000b0584caed8160c6d8bb5a1a42c0751b988baff535a488089b84`.

```lean
/-- A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure HomologicalComplex (c : ComplexShape ι) where
  X : ι → V
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬c.Rel i j → d i j = 0 := by cat_disch
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by cat_disch

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}

@[reassoc (attr := simp)]
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]

theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
```

`cochain_alias` — [lines 153–158](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalComplex.lean#L153-L158); SHA256 `7dc5c858538b2417090aef8327852df54aaeae95d4f28a7060fa11f3a0c86d70`.

```lean

/-- An `α`-indexed cochain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbrev CochainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)
```

### `Mathlib/CategoryTheory/Iso.lean`

[Mathlib/CategoryTheory/Iso.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Iso.lean)

Full SHA256: `b47eab342f3e7d08f4ff8d4a16d4580b0273d63f1a790b25560236c92d4cace7`. Git blob SHA1: `1d3e3cabd5c38fa072a3d9b7823b54bf206afd7b`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
```

`CategoryTheory_Iso` — [lines 47–62](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Iso.lean#L47-L62); SHA256 `99b7ba2647fd5879b510f98072a792784cec906fc6d00518d134eee59a519267`.

```lean
/-- An isomorphism (a.k.a. an invertible morphism) between two objects of a category.
The inverse morphism is bundled.

See also `CategoryTheory.Core` for the category with the same objects and isomorphisms playing
the role of morphisms. -/
@[stacks 0017, wikidata Q189112]
structure Iso {C : Type u} [Category.{v} C] (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : X ⟶ Y
  /-- The backwards direction of an isomorphism. -/
  inv : Y ⟶ X
  /-- Composition of the two directions of an isomorphism is the identity on the source. -/
  hom_inv_id : hom ≫ inv = 𝟙 X := by cat_disch
  /-- Composition of the two directions of an isomorphism in reverse order
  is the identity on the target. -/
  inv_hom_id : inv ≫ hom = 𝟙 Y := by cat_disch
```

### `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`

[Mathlib/Algebra/Homology/SpectralSequence/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean)

Full SHA256: `637c66009dfd06128b455e5593ca17e1144314b4996afcf7f2b26871c1c647b3`. Git blob SHA1: `4cf6043b1cd59cc410791df5c764e1ece0a9a675`. License: Apache-2.0.

```lean
/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_SpectralSequence` — [lines 33–45](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean#L33-L45); SHA256 `6aafc8cd6f66e9e0ddd882c9bc62b284940c8fb24e6043ce598dea46139f00aa`.

```lean

/-- Given an abelian category `C`, a sequence of complex shapes `c : ℤ → ComplexShape κ`
and a starting page `r₀ : ℤ`, a spectral sequence involves pages which are homological
complexes and isomorphisms saying that the homology of a page identifies to the next page. -/
structure SpectralSequence where
  /-- the `r`th page of a spectral sequence is an homological complex -/
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  /-- the isomorphism between the homology of the `r`-th page at an object `pq : κ`
  and the corresponding object on the next page -/
  iso (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence
```

`cohomological_indexing` — [lines 107–115](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean#L107-L115); SHA256 `c7294938a8c72957f538ec9a0e9c30c6b85c0cf975dad5cf3e40b0ce523896be`.

```lean

/-- A cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page. -/
abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))

/-- A `E₂`-cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2
```

### `Mathlib/Algebra/Homology/ShortComplex/Basic.lean`

[Mathlib/Algebra/Homology/ShortComplex/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Basic.lean)

Full SHA256: `97e6920aea53d672f60060967ce4bc4ef48d984c5ef48758b700b187a1983e3f`. Git blob SHA1: `dbed55d20ef07d8d5cc495ae730c264dc7ab3bde`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_ShortComplex` — [lines 30–48](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Basic.lean#L30-L48); SHA256 `7237fd38eda7b61c97cf835400c409c3fc50cff8f64db96bd01e5364d288ba82`.

```lean
variable (C) in
/-- A short complex in a category `C` with zero morphisms is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`. -/
structure ShortComplex where
  /-- the first (left) object of a `ShortComplex` -/
  {X₁ : C}
  /-- the second (middle) object of a `ShortComplex` -/
  {X₂ : C}
  /-- the third (right) object of a `ShortComplex` -/
  {X₃ : C}
  /-- the first morphism of a `ShortComplex` -/
  f : X₁ ⟶ X₂
  /-- the second morphism of a `ShortComplex` -/
  g : X₂ ⟶ X₃
  /-- the composition of the two given morphisms is zero -/
  zero : f ≫ g = 0 := by cat_disch

namespace ShortComplex
```

### `Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean`

[Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean)

Full SHA256: `0ca1a7c430c74bfadfb61f126109bc155953563526702a385d50d8d26ddbda80`. Git blob SHA1: `09103be0097f0884291ab0600425a78927802c0e`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_ShortComplex_LeftHomologyData` — [lines 42–65](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean#L42-L65); SHA256 `4c7d34e22278e6c7d5cbfe11b1e73258b51f4971124906058558ce0e7ea7e7eb`.

```lean
  {S₁ S₂ S₃ : ShortComplex C}

/-- A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K` -/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃` -/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)
```

`CategoryTheory_ShortComplex_LeftHomologyData_ofZeros` — [lines 207–221](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean#L207-L221); SHA256 `07301bd301032167dea53dbc9fa3b28c13953bb6de4d96064b829c3e670741d7`.

```lean
/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homology data on S -/
@[simps]
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf

@[simp] lemma ofZeros_f' (hf : S.f = 0) (hg : S.g = 0) :
```

### `Mathlib/CategoryTheory/Limits/IsLimit.lean`

[Mathlib/CategoryTheory/Limits/IsLimit.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Limits/IsLimit.lean)

Full SHA256: `b98c1fdd6ce5415360b6acae4a2c7c0de1d52312dca2e0c103d62f0067fd5b9a`. Git blob SHA1: `d260a878bda7df2fded444d9b58e9d08a2efa058`. License: Apache-2.0.

```lean
/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
```

`CategoryTheory_Limits_IsLimit` — [lines 46–57](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Limits/IsLimit.lean#L46-L57); SHA256 `1bf0b1e2762ca15f2ef13f2e5bb54c2a789541177cb0a80c74d8c59040f320c2`.

```lean

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`. -/
@[stacks 002E]
structure IsLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt) (_ : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by
    cat_disch
```

`CategoryTheory_Limits_IsColimit` — [lines 59–72](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Limits/IsLimit.lean#L59-L72); SHA256 `655b3fbcb07a0144ec431689d3359da3ae92b877ea362765764b17c31ff20296`.

```lean
/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`. -/
@[stacks 002F, to_dual]
structure IsColimit (t : Cocone F) where
  /-- `t.pt` maps to all other cocone covertices -/
  desc : ∀ s : Cocone F, t.pt ⟶ s.pt
  /-- The map `desc` makes the diagram with the natural transformations commute -/
  fac : ∀ (s : Cocone F) (j : J), dsimp% t.ι.app j ≫ desc s = s.ι.app j := by cat_disch
  /-- `desc` is the unique such map -/
  uniq : dsimp%
    ∀ (s : Cocone F) (m : t.pt ⟶ s.pt) (_ : ∀ j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s := by
    cat_disch

attribute [reassoc (attr := simp)] IsLimit.fac IsColimit.fac
```

### `Mathlib/Algebra/Homology/ShortComplex/Homology.lean`

[Mathlib/Algebra/Homology/ShortComplex/Homology.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean)

Full SHA256: `dd6997af035b48adedaaefe9cc75c27fa628e090f2032c1ce7e7e20e998f67ef`. Git blob SHA1: `deb9d618262e919e690bb9b05f394b56ab67b91a`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_ShortComplex_HomologyData` — [lines 47–62](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L47-L62); SHA256 `63efe73e3bcafdacf40d0e0b602acc4aede250451758b6bd0ce93548c751961f`.

```lean

/-- A homology data for a short complex consists of two compatible left and
right homology data -/
structure HomologyData where
  /-- a left homology data -/
  left : S.LeftHomologyData
  /-- a right homology data -/
  right : S.RightHomologyData
  /-- the compatibility isomorphism relating the two dual notions of
  `LeftHomologyData` and `RightHomologyData` -/
  iso : left.H ≅ right.H
  /-- the pentagon relation expressing the compatibility of the left
  and right homology data -/
  comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p := by cat_disch

attribute [reassoc (attr := simp)] HomologyData.comm
```

`CategoryTheory_ShortComplex_HasHomology` — [lines 213–219](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L213-L219); SHA256 `65944169e5cdaf6b340aab6306ebd6e73787dd39215737a812f7a2374c244b51`.

```lean
/-- A short complex `S` has homology when there exists a `S.HomologyData` -/
class HasHomology : Prop where
  /-- the condition that there exists a homology data -/
  condition : Nonempty S.HomologyData

/-- A chosen `S.HomologyData` for a short complex `S` that has homology -/
noncomputable def homologyData [HasHomology S] : S.HomologyData := HasHomology.condition.some
```

`CategoryTheory_ShortComplex_homologyData` — [lines 217–219](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L217-L219); SHA256 `ad95ae08019eda019fcaf4da50b9995104ba6c99a348fef8a6b3e3d068333627`.

```lean

/-- A chosen `S.HomologyData` for a short complex `S` that has homology -/
noncomputable def homologyData [HasHomology S] : S.HomologyData := HasHomology.condition.some
```

`CategoryTheory_ShortComplex_homology` — [lines 381–384](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L381-L384); SHA256 `d2efa3435f46e7c11e0a0b72c805fb86d3a24623e9e5c673fa1ac05307ad98d9`.

```lean
variable (S)

/-- The homology of a short complex is the `left.H` field of a chosen homology data. -/
noncomputable def homology [HasHomology S] : C := S.homologyData.left.H
```

`CategoryTheory_ShortComplex_LeftHomologyData_homologyIso` — [lines 397–402](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L397-L402); SHA256 `1e06c6cd4ab82c580fc6409d819b02725aa3e7717e034f42cc83989cd4ec5d24`.

```lean

/-- When a short complex has homology, its homology can be computed using
any left homology data. -/
noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

```

`canonical_homology_projection` — [lines 975–988](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/Homology.lean#L975-L988); SHA256 `1ebbf7f47602bb5afd1ee6662c9357477ac584fca8e47e14d407e1c54953ea22`.

```lean

@[reassoc (attr := simp)]
lemma LeftHomologyData.homologyπ_comp_homologyIso_hom (h : S.LeftHomologyData) :
    S.homologyπ ≫ h.homologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_hom, Iso.symm_hom, assoc, Iso.hom_inv_id_assoc,
    leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]
lemma LeftHomologyData.π_comp_homologyIso_inv (h : S.LeftHomologyData) :
    h.π ≫ h.homologyIso.inv = h.cyclesIso.inv ≫ S.homologyπ := by
  dsimp only [homologyπ, homologyIso]
  simp only [Iso.trans_inv, Iso.symm_inv, π_comp_leftHomologyIso_inv_assoc]

```

### `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`

[Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean)

Full SHA256: `6d1c0eedf5e2ca3fc3d1c1693cc51c35f5be3045403dc814637d977872d30b30`. Git blob SHA1: `27731c25d8f93ed52053070198f138d58bf08312`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`HomologicalComplex_shortComplexFunctor'` — [lines 35–44](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean#L35-L44); SHA256 `00088ac0f869efe871bf43e88d10bc0d721e19bdd3a0fcfd2553e91b7a6d4440`.

```lean
/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
@[simps]
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

```

`HomologicalComplex_homology` — [lines 86–91](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean#L86-L91); SHA256 `7d1a78d14816c879747652f494099a6c1216fe3fb909cd60e31c11e12e16aaeb`.

```lean

variable [K.HasHomology i]

/-- The homology in degree `i` of a homological complex. -/
noncomputable def homology := (K.sc i).homology

```

`HomologicalComplex_homologyIsoSc'` — [lines 926–930](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean#L926-L930); SHA256 `da2b18d40f0f1f80093ce329af499870e1220cc94a8af60d200727884c513c50`.

```lean
/-- The opcycles of a homological complex in degree `j` can be computed
by specifying a choice of `c.prev j` and `c.next j`. -/
noncomputable def homologyIsoSc' : K.homology j ≅ (K.sc' i j k).homology :=
  ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

```

`shortcomplex_aliases` — [lines 64–72](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean#L64-L72); SHA256 `8a420f4e465e06ad95fc324f07cfd6bd2825269030c2fb8dbf40c1f10a23372b`.

```lean

/-- The short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
abbrev sc' := (shortComplexFunctor' C c i j k).obj K

/-- The short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
noncomputable abbrev sc := (shortComplexFunctor C c i).obj K

/-- The canonical isomorphism `K.sc j ≅ K.sc' i j k` when `c.prev j = i` and `c.next j = k`. -/
noncomputable abbrev isoSc' (hi : c.prev j = i) (hk : c.next j = k) :
```

### `Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean`

[Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean)

Full SHA256: `24dd94f0c8dbc9ed5cb75d4c0281ff69cbd589156887cbff723046c2ecf9de2c`. Git blob SHA1: `2b633dbfb07d98f6f9a3fc157c6008f94f98e7d1`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_ShortComplex_moduleCatLeftHomologyData` — [lines 92–111](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L92-L111); SHA256 `c07796276f3576d07a6bdecbc259118663348a098568ca553ee7135b11021e12`.

```lean

/-- The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`. -/
abbrev moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g.hom :=
  S.f.hom.codRestrict _ <| S.moduleCat_zero_apply

set_option backward.defeqAttrib.useBackward true in
/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. The projections to `K` and `H` are
not simp lemmas because the generic lemmas about `LeftHomologyData` are more useful here. -/
@[simps! K H i_hom π_hom]
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ↧S.g.hom.ker
  H := ↧(S.g.hom.ker ⧸ S.moduleCatToCycles.range)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ := by aesop
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

```

`CategoryTheory_ShortComplex_moduleCatHomologyIso` — [lines 168–188](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L168-L188); SHA256 `486073f2b898ba282a4a3c8c83073a60de8f28130ebd3c0f1d1e7523559f31e7`.

```lean

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `LinearMap.ker S.g` by the image of
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g`. -/
noncomputable def moduleCatHomologyIso :
    S.homology ≅ S.moduleCatLeftHomologyData.H :=
  S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]
lemma π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π :=
  S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]
lemma moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv :=
  S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

```

### `Mathlib/Algebra/Homology/TotalComplex.lean`

[Mathlib/Algebra/Homology/TotalComplex.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean)

Full SHA256: `e223f14193a2a9de9cb0d62c9eaf71a4d5ce90d644a8b088dd3e40c7b7ca4e9e`. Git blob SHA1: `2e4d80bf9f4c4592c727bcff16c6ad48c85b8231`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`HomologicalComplex₂_total` — [lines 263–269](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean#L263-L269); SHA256 `26f5bb3cc5388d2cc13f54e6a9a4ef526d8289cce0e75e25dd4e0618b2c7fbfb`.

```lean
/-- The total complex of a bicomplex. -/
@[simps -isSimp d, implicit_reducible]
noncomputable def total : HomologicalComplex C c₁₂ where
  X := K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    rw [K.D₁_shape c₁₂ _ _ h₁₂, K.D₂_shape c₁₂ _ _ h₁₂, zero_add]
```

`HomologicalComplex₂_ιTotal` — [lines 271–276](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean#L271-L276); SHA256 `ff9d85e8949d87a9c965337018556af2c5e0b62984546e87ac7fe68127285eb8`.

```lean
/-- The inclusion of a summand in the total complex. -/
noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

```

`HomologicalComplex₂_d₁` — [lines 59–65](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean#L59-L65); SHA256 `040308abc478d66259733f6c54ce0df1404e9b667dfd8e608b3d960da97fe74a`.

```lean

/-- The horizontal differential in the total complex on a given summand. -/
noncomputable def d₁ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

```

`HomologicalComplex₂_d₂` — [lines 66–72](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean#L66-L72); SHA256 `726427a8bf5778d571315b7dec0fcda7804cff42c09ef6a45443ff5e0cb8c777`.

```lean
/-- The vertical differential in the total complex on a given summand. -/
noncomputable def d₂ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

set_option backward.isDefEq.respectTransparency.types false in
```

`hasTotal_alias` — [lines 41–45](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/TotalComplex.lean#L41-L45); SHA256 `cafcc0961ba42ad60e2161431431ae79f41b7736469e19317d9a57edfdd305ce`.

```lean
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

/-- A bicomplex has a total bicomplex if for any `i₁₂ : I₁₂`, the coproduct
of the objects `(K.X i₁).X i₂` such that `ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂` exists. -/
abbrev HasTotal := K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)
```

### `Mathlib/CategoryTheory/GradedObject.lean`

[Mathlib/CategoryTheory/GradedObject.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/GradedObject.lean)

Full SHA256: `6c2306dbc013a65c032fa18d9ad4194aaf56903faa3304bed7a8f35b919e6fb6`. Git blob SHA1: `9e683eed1e19d5c3e122c6befca999a4141f0051`. License: Apache-2.0.

```lean
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
```

`CategoryTheory_GradedObject_mapObj` — [lines 302–307](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/GradedObject.lean#L302-L307); SHA256 `50dd7951d1a5424ee8ec0c6fbe2355ab11fc56dc91f248f9d0ce69a31c91119e`.

```lean
variable [X.HasMap p] [Y.HasMap p]

/-- Given `X : GradedObject I C` and `p : I → J`, `X.mapObj p` is the graded object by `J`
which in degree `j` consists of the coproduct of the `X i` such that `p i = j`. -/
noncomputable def mapObj : GradedObject J C := fun j => ∐ (X.mapObjFun p j)

```

`hasMap_alias` — [lines 285–294](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/GradedObject.lean#L285-L294); SHA256 `314aec75466aeec12fd58f112828fa9397c3203189f171144db892d59f6fa7d3`.

```lean
/-- If `X : GradedObject I C` and `p : I → J`, `X.mapObjFun p j` is the family of objects `X i`
for `i : I` such that `p i = j`. -/
abbrev mapObjFun (j : J) (i : p ⁻¹' {j}) : C := X i

variable (j : J)

/-- Given `X : GradedObject I C` and `p : I → J`, `X.HasMap p` is the condition that
for all `j : J`, the coproduct of all `X i` such `p i = j` exists. -/
abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (X.mapObjFun p j)

```

### `Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean`

[Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean)

Full SHA256: `36305292f29ec1870be84d907137757b7cb7eb55a1e5638d8092712be80128e5`. Git blob SHA1: `db7db3eb3f9bc867e623dbeaff836577df828c1e`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`CategoryTheory_ShortComplex_RightHomologyData` — [lines 42–62](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean#L42-L62); SHA256 `7ebcbf0f73259a41458e7a86bc6511b277d9b307ba1365d53c07fc2581ba45bc`.

```lean
/-- A right homology data for a short complex `S` consists of morphisms `p : S.X₂ ⟶ Q` and
`ι : H ⟶ Q` such that `p` identifies `Q` with the cokernel of `f : S.X₁ ⟶ S.X₂`,
and that `ι` identifies `H` with the kernel of the induced map `g' : Q ⟶ S.X₃` -/
structure RightHomologyData where
  /-- a choice of cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  Q : C
  /-- a choice of kernel of the induced morphism `S.g' : S.Q ⟶ X₃` -/
  H : C
  /-- the projection from `S.X₂` -/
  p : S.X₂ ⟶ Q
  /-- the inclusion of the (right) homology in the chosen cokernel of `S.f` -/
  ι : H ⟶ Q
  /-- the cokernel condition for `p` -/
  wp : S.f ≫ p = 0
  /-- `p : S.X₂ ⟶ Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  hp : IsColimit (CokernelCofork.ofπ p wp)
  /-- the kernel condition for `ι` -/
  wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
  /-- `ι : H ⟶ Q` is a kernel of `S.g' : Q ⟶ S.X₃` -/
  hι : IsLimit (KernelFork.ofι ι wι)

```

### `Mathlib/Algebra/Homology/ComplexShapeSigns.lean`

[Mathlib/Algebra/Homology/ComplexShapeSigns.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShapeSigns.lean)

Full SHA256: `010025013958bdba09f6a269b8620266a3ab55d058a2834f19f5b0cc291a16ae`. Git blob SHA1: `66ec22c612dfad9273a19a887aa51d7092853836`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
```

`TotalComplexShape` — [lines 37–53](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShapeSigns.lean#L37-L53); SHA256 `d803e9e8152a9cb58a4162def841562b63d840b592ddbee7c8bb0eaa2b264dbc`.

```lean
/-- A total complex shape for three complex shapes `c₁`, `c₂`, `c₁₂` on three types
`I₁`, `I₂` and `I₁₂` consists of the data and properties that will allow the construction
of a total complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` which
sends `K` to a complex which in degree `i₁₂ : I₁₂` consists of the coproduct
of the `(K.X i₁).X i₂` such that `π ⟨i₁, i₂⟩ = i₁₂`. -/
class TotalComplexShape where
  /-- a map on indices -/
  π : I₁ × I₂ → I₁₂
  /-- the sign of the horizontal differential in the total complex -/
  ε₁ : I₁ × I₂ → ℤˣ
  /-- the sign of the vertical differential in the total complex -/
  ε₂ : I₁ × I₂ → ℤˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

```

`ComplexShape_TensorSigns` — [lines 117–125](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShapeSigns.lean#L117-L125); SHA256 `356caa154df9a3ed441f24e65d4fb9333b70fc88ee46ad4c29162088c8d77367`.

```lean
/-- If `I` is an additive monoid and `c : ComplexShape I`, `c.TensorSigns` contains the data of
map `ε : I → ℤˣ` and properties which allows the construction of a `TotalComplexShape c c c`. -/
class TensorSigns where
  /-- the signs which appear in the vertical differential of the total complex -/
  ε' : Multiplicative I →* ℤˣ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε'_succ (p q : I) (hpq : c.Rel p q) : ε' q = - ε' p

```

`integer_sign` — [lines 174–193](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShapeSigns.lean#L174-L193); SHA256 `2ff5617927b3008ecad44f8e83abdfca9aa7579728f18b21cd1a409ff511e0ef`.

```lean
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one, neg_neg]

@[simp]
lemma ε_down_ℕ (n : ℕ) : (ComplexShape.down ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : TensorSigns (ComplexShape.up ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]

@[simp]
lemma ε_up_ℤ (n : ℤ) : (ComplexShape.up ℤ).ε n = n.negOnePow := rfl

```

`total_shape_signs` — [lines 154–164](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/ComplexShapeSigns.lean#L154-L164); SHA256 `f55dc56702a45d44c18fff1501e624a4f108c3b45f7297475e89b21ad17bd396`.

```lean

@[simps]
instance : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul, one_mul, mul_one, c.ε_succ h, neg_neg]
```

### `Mathlib/Algebra/Ring/NegOnePow.lean`

[Mathlib/Algebra/Ring/NegOnePow.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Ring/NegOnePow.lean)

Full SHA256: `7f22251f2ae04c10d52163a31f257305e91e84d72a4589882208152c2d841f7e`. Git blob SHA1: `0580a32e48fb1492c513b193ad5b6ec73009f464`. License: Apache-2.0.

```lean
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
```

`Int_negOnePow` — [lines 29–37](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Ring/NegOnePow.lean#L29-L37); SHA256 `7b865f763de5410fb5d18fdb0f9cc1851e144a53c80db1ed67d8dc9c28535145`.

```lean
/-- The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`. -/
def negOnePow (n : ℤ) : ℤˣ := (-1 : ℤˣ) ^ n

lemma negOnePow_def (n : ℤ) : n.negOnePow = (-1 : ℤˣ) ^ n := rfl

lemma negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow :=
  zpow_add _ _ _

```

### `Mathlib/Algebra/Module/Equiv/Defs.lean`

[Mathlib/Algebra/Module/Equiv/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Defs.lean)

Full SHA256: `fea6294b3b6d6bdda0f62eb99a5977e4a73bbca7bf98e1be83c158c79e0e197a`. Git blob SHA1: `c755408694c1453e874ea6512506b4713679f8a2`. License: Apache-2.0.

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
```

`LinearEquiv` — [lines 48–66](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Equiv/Defs.lean#L48-L66); SHA256 `b331fdcb3b620b9b3c29a95e4efda156ff064f392497167c2615b7fbdabe4bba`.

```lean
/-- A linear equivalence is an invertible linear map. -/
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toAddEquiv

/-- The backwards directed function underlying a linear equivalence. -/
add_decl_doc LinearEquiv.invFun

/-- `LinearEquiv.invFun` is a right inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.right_inv

```

### `Mathlib/Algebra/Module/Submodule/Equiv.lean`

[Mathlib/Algebra/Module/Submodule/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Equiv.lean)

Full SHA256: `12d18d55d3b5a01c63386566a3797fb3ddc4b6ea78873226cd93a8a80a65e6b9`. Git blob SHA1: `d6236473dd0525c4ffa2d246243a62909320b512`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

`LinearEquiv_ofBijective` — [lines 182–191](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Equiv.lean#L182-L191); SHA256 `84ff0d3f3de4851f3441e3a65f44801329d3807e652668c9a8e156872f989c88`.

```lean
/-- A bijective linear map is a linear equivalence. -/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans <| ofTop _ <|
    LinearMap.range_eq_top.2 hf.surjective

@[simp]
theorem ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) :
    ofBijective f hf x = f x :=
  rfl
```

### `Mathlib/Algebra/Homology/HomologicalBicomplex.lean`

[Mathlib/Algebra/Homology/HomologicalBicomplex.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalBicomplex.lean)

Full SHA256: `e5360697c04f6d6507d52f0adfc72b79645b77b5ce9e26446a250937010af608`. Git blob SHA1: `2e9e8bf964dad97bf4b2c7964986b354d3a01fcd`. License: Apache-2.0.

```lean
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
```

`bicomplex_alias` — [lines 32–40](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalBicomplex.lean#L32-L40); SHA256 `178e20e9ce3d986352ef99a87e4d891f90feab3e642547a3a60b32bc35fdc61d`.

```lean
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`. -/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

```

`commuting_square` — [lines 138–143](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/HomologicalBicomplex.lean#L138-L143); SHA256 `f81056ec3624f906b92776f525b0288da6430778c6b3d3c7a56162c2e71c1a91`.

```lean
@[reassoc]
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

@[reassoc (attr := simp)]
```

### `Mathlib/Algebra/Module/Submodule/Lattice.lean`

[Mathlib/Algebra/Module/Submodule/Lattice.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean)

Full SHA256: `6d143772606afa67740f152df5cad2263a867ffb4a7314686c98cba5b9efb430`. Git blob SHA1: `1b5678a24211e4176f5c7a7167075d8aea7fb3e7`. License: Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
```

`submodule_bottom` — [lines 50–55](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L50-L55); SHA256 `d18e9cd05d310518a6726c6621e30dd9c2809c4ae950a2820a14d63837537e4b`.

```lean

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩
```

`submodule_top` — [lines 129–134](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L129-L134); SHA256 `ed0d96746cc671fab01d8a1bc7287d03e1d84755452fa1ae7dd0b6272fcf1044`.

```lean
/-- The universal set is the top element of the lattice of submodules. -/
instance : Top (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ ↦ trivial }⟩

```

`submodule_lattice` — [lines 180–216](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/Lattice.lean#L180-L216); SHA256 `98e321adbc678b3e41be924048492a3033c488d477a616fd9a7bceb7d3aead12`.

```lean
instance : InfSet (Submodule R M) :=
  ⟨fun S ↦
    { carrier := ⋂ s ∈ S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

protected theorem isGLB_sInf {S : Set (Submodule R M)} : IsGLB S (sInf S) :=
  .of_image SetLike.coe_subset_coe isGLB_biInf

instance : Min (Submodule R M) :=
  ⟨fun p q ↦
    { carrier := p ∩ q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩

instance completeLattice : CompleteLattice (Submodule R M) where
  sup a b := sInf { x | a ≤ x ∧ b ≤ x }
  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ ↦ h
  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ ↦ h
  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf _ _ _ := Set.subset_inter
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}
  isLUB_sSup _ := isGLB_upperBounds.mp Submodule.isGLB_sInf
  isGLB_sInf _ := Submodule.isGLB_sInf

@[simp]
theorem coe_inf : ↑(p ⊓ q) = (p ∩ q : Set M) :=
  rfl

@[simp]
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl
```

### `Mathlib/Algebra/Category/ModuleCat/Colimits.lean`

[Mathlib/Algebra/Category/ModuleCat/Colimits.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Colimits.lean)

Full SHA256: `56240e276c94d5a20573b59aa01a789fbc55f3c8a2e6377810912600926d385b`. Git blob SHA1: `467890248156563a42f746a82a5be8f05ff3a879`. License: Apache-2.0.

```lean
/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
```

`modulecat_colimits` — [lines 119–150](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Colimits.lean#L119-L150); SHA256 `c977278abaae57fe94c6152471f98120426f32a2bff053043ec58750bb7d9229`.

```lean
instance hasColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    HasColimitsOfShape J (ModuleCat.{w'} R) where

noncomputable instance reflectsColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    ReflectsColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

instance hasColimitsOfSize [HasColimitsOfSize.{v, u} AddCommGrpCat.{w'}] :
    HasColimitsOfSize.{v, u} (ModuleCat.{w'} R) where

noncomputable instance forget₂PreservesColimitsOfShape
    [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    PreservesColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

noncomputable instance forget₂PreservesColimitsOfSize
    [HasColimitsOfSize.{u, v} AddCommGrpCat.{w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

noncomputable instance
    [HasColimitsOfSize.{u, v} AddCommGrpMax.{w, w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{max w w'} R) AddCommGrpCat) where

instance : HasFiniteColimits (ModuleCat.{w'} R) := inferInstance

-- Sanity checks, just to make sure typeclass search can find the instances we want.
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max v u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance
```

