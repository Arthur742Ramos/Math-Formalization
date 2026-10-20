# Material imported definitions: the Baire product theorem for Choquet spaces

Mathlib is pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55` and Lean to `leanprover/lean4:v4.35.0-rc2`. This inventory follows actual selected statements and their material proof dependencies. It preserves exact upstream attribution and source bytes; it does not claim that hashes or an automated check establish mathematical fidelity or completeness.

The eight selected theorems have no Comparator definition holes. `OpenMove`, `history`, `Follows`, `SecondWins`, `AlphaFavorable`, `SecondStrategy`, and the particular `metricStrategy` remain fixed model/proof dependencies. History retains all earlier opponent moves, newest first; a strategy receives the current opponent move separately. Nonempty spaces have the ordinary full-history second-player game. Empty-space alpha-favorability is an explicitly vacuous extension, not a legal empty-space play.

The first factor needs only its arbitrary supplied topology and Baire property. The general second factor needs a winning full-history second strategy, without a metric/separation/countability premise. The complete-metric specialization uses the second factor’s inherited metric topology. The product uses the usual product topology, evidenced by its projection-induced definition and the proved local-open-rectangle characterization.

The fiber conclusion has quantifiers `∀ x ∈ G, ∃ y ∈ V, ∀ n, (x,y) ∈ D n`: the same y works for every n, but it may depend on x and the prescribed nonempty open V. It does not assert density of the entire vertical section or second countability.

## Meaning and selected-use inventory

### `BaireSpace`

Role: `hypothesis-and-conclusion`. Declaration kind: `class`. Bridge form: `class-fields`.

Every natural-number-indexed intersection of dense open sets is dense. No separation or nonempty hypothesis.

Class field baire_property quantifies D : ℕ → Set X with every D n open and dense in the supplied topology, concluding Dense of the entire intersection. In the witness proof these are dense disjoint-family domains; in each product conclusion the topology is the usual binary product topology fixed by instTopologicalSpaceProd. No countability of either factor or of the disjoint label family is supplied.

Selected uses: `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `BaireSpace`. Retained bridge/dependency excerpts: `BaireSpace`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Dense`

Role: `hypothesis-and-conclusion`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

Every ambient point belongs to the closure; equivalently every nonempty open set meets the set.

Closure is the intersection of all closed supersets. dense_iff_inter_open proves the nonempty-open-intersection characterization; it is not claimed definitionally equal to Dense. The witness theorem concludes a dense subset G of the whole first factor, but only one common fiber point inside each prescribed nonempty open V, not density of an entire vertical section.

Selected uses: `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Dense`. Retained bridge/dependency excerpts: `Dense`, `dense_iff_inter_open`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Set.PairwiseDisjoint`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

For every pair of distinct labels in the chosen family, their image sets are disjoint.

Set.Pairwise quantifies all distinct labels in the selected family. The image sets must have empty intersection. Distinct labels with equal inhabited image sets therefore violate pairwise disjointness. The proof uses this to identify the unique parent over a fixed first-coordinate point; no countability restriction or universe identification is imposed.

Selected uses: `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `PairwiseDisjoint`. Retained bridge/dependency excerpts: `PairwiseDisjoint`, `Set.Pairwise`, `Disjoint`, `set-disjoint`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `IsOpen`

Role: `definition`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The open-set predicate supplied by the given ambient topological-space structure.

The definition projects the current ambient TopologicalSpace. General factor topologies have no separation or countability requirement. In metric results the second-factor topology comes from MetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace, with uniformity/topology compatibility retained; the first factor remains arbitrary.

Selected uses: `ChoquetProduct.follows_intersection_eq`, `ChoquetProduct.exists_compatiblePlay`, `ChoquetProduct.alphaFavorable_of_isEmpty`, `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `topology-open-closed`. Retained bridge/dependency excerpts: `topology-open-closed`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `closure`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The smallest closed superset: the intersection of every closed set containing the given set.

Literal intersection of all closed supersets; IsClosed means open complement. Maximal disjoint refinements give density by closure containment. This imports neither compactness nor a separation condition.

Selected uses: `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `interior-closure`. Retained bridge/dependency excerpts: `interior-closure`, `topology-open-closed`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Set.Nonempty`

Role: `definition`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

There exists one element belonging to the set. A common point belongs to every move; one different point per round is insufficient.

Set.Nonempty is existential membership, with no cardinality or uniqueness requirement. Winning means one y belongs to every response in an infinite compatible play; a separate y for each round is insufficient. Fiber witnesses quantify one y in prescribed V that works simultaneously for all D n. Empty types have no OpenMove, so the empty-space winning-strategy extension is vacuous, not a claimed legal play.

Selected uses: `ChoquetProduct.follows_intersection_eq`, `ChoquetProduct.exists_compatiblePlay`, `ChoquetProduct.alphaFavorable_of_isEmpty`, `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Set.Nonempty`. Retained bridge/dependency excerpts: `Set.Nonempty`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `IsEmpty`

Role: `hypothesis`. Declaration kind: `class`. Bridge form: `class-fields`.

The type has no elements: every element implies False.

IsEmpty.false : Y → False gives type emptiness. It does not make the subtype of legal moves inhabited. A total second-strategy function exists on an empty domain and has no compatible infinite opponent sequence; AlphaFavorable is extended to the empty type through this vacuity.

Selected uses: `ChoquetProduct.alphaFavorable_of_isEmpty`.

Definition excerpt: `IsEmpty`. Retained bridge/dependency excerpts: `IsEmpty`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `TopologicalSpace`

Role: `definition`. Declaration kind: `class`. Bridge form: `class-fields`.

An open-set predicate containing the whole space and closed under binary intersections and arbitrary unions.

Data carrying an arbitrary open predicate and its univ/intersection/arbitrary-union axioms, not a proposition. The source instTopologicalSpaceProd is the infimum of the two projection-induced topologies; isOpen_prod_iff proves the local open-rectangle characterization. For metric Y, the supplied superclass topology is constrained by the metric uniformity, not silently replaced by an unrelated topology.

Selected uses: `ChoquetProduct.follows_intersection_eq`, `ChoquetProduct.exists_compatiblePlay`, `ChoquetProduct.alphaFavorable_of_isEmpty`, `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `TopologicalSpace`. Retained bridge/dependency excerpts: `TopologicalSpace`, `topology-open-closed`, `product-topology`, `isOpen_prod_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `IsGδ`

Role: `conclusion`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

A countable intersection of open sets in the given topology.

The literal definition uses a countable Set (Set X), not an assumed nonempty family. isGδ_iff_eq_iInter_nat is the proved conversion to a natural-number-indexed open family. It is an equivalence theorem, not definitional equality. G is a subset of X, not a product section.

Selected uses: `ChoquetProduct.exists_dense_isGdelta_fiber_witness`, `ChoquetProduct.baireSpace_prod`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `IsGδ`. Retained bridge/dependency excerpts: `IsGδ`, `isGδ_iff_eq_iInter_nat`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `MetricSpace`

Role: `hypothesis`. Declaration kind: `class`. Bridge form: `class-fields`.

A real-valued symmetric triangle-inequality distance vanishing exactly when its points are equal, with its compatible topology, uniformity and bornology.

MetricSpace extends PseudoMetricSpace and adds eq_of_dist_eq_zero. PseudoMetricSpace supplies Dist.dist, self-zero, symmetry, triangle inequality, an extended distance compatible with real distance, the uniformity_dist equality and compatible bornology. No completeness, local compactness, properness, separability, or compactness of closed balls follows from this class alone. Metric results use this inherited topology, with no independently arbitrary TopologicalSpace Y.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `MetricSpace`. Retained bridge/dependency excerpts: `MetricSpace`, `PseudoMetricSpace`, `Dist`, `UniformSpace`, `Metric.isOpen_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `PseudoMetricSpace`

Role: `proof-dependency`. Declaration kind: `class`. Bridge form: `class-fields`.

A real-valued pseudometric, its compatible extended distance, uniformity and bornology; zero distance need not separate points.

Class fields require dist_self, dist_comm, dist_triangle; uniformity_dist identifies 𝓤 with the infimum of principal distance-entourages. UniformSpace.nhds_eq_comap_uniformity connects that uniformity to the stored topology. The bornology cobounded_sets field identifies metric bounded sets. These are constraints on stored structures, not an arbitrary topology plus a distance.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `PseudoMetricSpace`. Retained bridge/dependency excerpts: `PseudoMetricSpace`, `Dist`, `UniformSpace`, `Metric.isOpen_iff`, `Bornology`, `Metric.isBounded_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `UniformSpace`

Role: `proof-dependency`. Declaration kind: `class`. Bridge form: `class-fields`.

A uniformity filter on pairs, symmetric and closed under entourage composition, with compatible stored topology.

The class extends TopologicalSpace and includes symm, comp and nhds_eq_comap_uniformity. Diagonal/reflexivity follows from neighborhood compatibility; it is explicit in the separate Core description. 𝓤 is the uniformity projection. Filter order is reverse inclusion of set collections; nhds denotes all neighborhoods of the current topology.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `UniformSpace`. Retained bridge/dependency excerpts: `UniformSpace`, `UniformSpace.Core`, `Filter`, `Filter.principal`, `Filter.map-Tendsto`, `Filter.comap`, `nhds`, `mem_nhds_iff`, `Filter.order`, `Filter.product`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `CompleteSpace`

Role: `hypothesis`. Declaration kind: `class`. Bridge form: `class-fields`.

Every nontrivial Cauchy filter has a limit in the space.

The class field quantifies every Filter Y with Cauchy, not merely sequences. Cauchy expands to NeBot and f×f≤𝓤. IsComplete univ is proved equivalent to CompleteSpace. In metric spaces the inherited distance/topology yields ordinary metric completeness. Empty metric spaces are allowed, since no nontrivial Cauchy filter exists on an empty type. The proof uses the credited closed/bounded finite-intersection diameter-to-zero theorem; no compactness of balls is assumed.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `CompleteSpace`. Retained bridge/dependency excerpts: `CompleteSpace`, `Cauchy`, `IsComplete`, `completeSpace_iff_isComplete_univ`, `Metric.cauchySeq_iff`, `Metric.nonempty_iInter_of_nonempty_biInter`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Cauchy`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

A nontrivial filter whose pairs become arbitrarily uniformly close.

Literal conjunction NeBot f ∧ f×ˢf≤𝓤. NeBot is a separate class asserting f≠⊥; Mathlib filters themselves allow the improper bottom filter. cauchy_iff proves the small-set entourage description, and Metric.cauchy_iff proves its epsilon-distance form. The nontriviality guard is essential to avoid false empty-space limits.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Cauchy`. Retained bridge/dependency excerpts: `Cauchy`, `cauchy_iff`, `Filter.NeBot`, `Filter`, `Metric.cauchy_iff`, `Filter.order`, `Filter.product`, `Filter.mem_prod_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `IsComplete`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

Every Cauchy filter supported on a set has a limit in that same set.

Literally ∀f,Cauchy f→f≤𝓟s→∃x∈s,f≤𝓝x. Principal-filter support means s∈f. The limit belongs to s; mere ambient convergence is insufficient. CompleteSpace is equivalent to IsComplete univ by a proved theorem.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `IsComplete`. Retained bridge/dependency excerpts: `IsComplete`, `Cauchy`, `Filter.principal`, `nhds`, `completeSpace_iff_isComplete_univ`, `Filter.le_principal_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `CauchySeq`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

A map whose image of the atTop filter is Cauchy; for natural-number sequences this is the usual epsilon-tail condition.

The definition supports arbitrary preorders, but the semantic bridge specializes to ℕ: ∀ε>0,∃N,∀m≥N,∀n≥N,dist(a m)(a n)<ε. This is a proved characterization, not the literal defining expression; the latter is Cauchy (Filter.map a atTop). The imported Cantor-intersection theorem uses this completeness infrastructure.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `CauchySeq`. Retained bridge/dependency excerpts: `CauchySeq`, `Cauchy`, `Filter.atTop`, `Filter.map-Tendsto`, `Metric.cauchySeq_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Filter.Tendsto`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The image filter lies below the target filter: every target neighborhood has a source-large preimage.

Literally Filter.map f l₁≤l₂. map encodes preimages, and tendsto_def states the equivalent membership form. In the metric proof l₁=atTop on ℕ, l₂=𝓝0 in ℝ for diameter convergence. This asserts a limit of the whole tail, without an implicit subsequence or a replacement topology.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Filter.map-Tendsto`. Retained bridge/dependency excerpts: `Filter.map-Tendsto`, `Filter.tendsto_def`, `Filter.atTop`, `nhds`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Metric.ball`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The open distance ball centered at x of real radius r: points y with dist y x<r.

Literal strict inequality. metricStrategy uses a positive radius at most (1/2)^history.length, chosen so the corresponding closed ball lies inside the current nonempty open move. The helper and metricStrategy are fixed proof dependencies, not Comparator definition holes. A center and positive radius are chosen from a legal move; no global Nonempty Y premise is added.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Metric.ball`. Retained bridge/dependency excerpts: `Metric.ball`, `MetricSpace`, `PseudoMetricSpace`, `Metric.isOpen_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Metric.closedBall`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The closed distance ball centered at x of radius r: points y with dist y x≤r.

Literal non-strict inequality. The successive chosen closed ball is contained in the preceding open response; this strict/open trapping lets a point in all closed traps belong to every actual open response. Closed balls are bounded and closed in metric spaces, with no claim they are compact.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Metric.closedBall`. Retained bridge/dependency excerpts: `Metric.closedBall`, `Metric.ball`, `Metric.nonempty_iInter_of_nonempty_biInter`, `Metric.isBounded_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Bornology.IsBounded`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

Boundedness in the compatible metric bornology; equivalently all pairwise distances on the set are bounded by some real constant.

Literally IsCobounded of the complement. Bornology stores a cobounded filter, and PseudoMetricSpace.cobounded_sets constrains that filter to the distance bornology. Metric.isBounded_iff is the proved pairwise-distance bound; it is not the literal general bornology definition. Boundedness alone implies neither closedness nor compactness.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Bornology.IsBounded`. Retained bridge/dependency excerpts: `Bornology.IsBounded`, `Bornology`, `PseudoMetricSpace`, `Metric.isBounded_iff`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Metric.diam`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The real-valued diameter is ENNReal.toReal of the extended diameter.

This definition is not an unconditional finite supremum: ENNReal.toReal maps infinity to zero. Therefore boundedness is material in the credited finite-intersection theorem. Every chosen closed ball is bounded and its real diameter is bounded by twice its radius, so diameter-to-zero is used on finite extended diameters. No unbounded-set or compact-ball claim is made.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Metric.diam`. Retained bridge/dependency excerpts: `Metric.diam`, `Metric.ediam`, `Metric.nonempty_iInter_of_nonempty_biInter`, `Metric.isBounded_iff`, `ENNReal.toReal_top`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

### `Metric.ediam`

Role: `proof-dependency`. Declaration kind: `def`. Bridge form: `literal-unfolding`.

The extended nonnegative diameter is the supremum of edist x y over all x and y in the set.

The supremum ranges over both point-membership proofs and may be infinity. PseudoMetricSpace.edist_dist identifies edist with ENNReal.ofReal of dist. This distinguishes the extended supremum from Metric.diam, which converts to ℝ and sends infinity to zero.

Selected uses: `ChoquetProduct.metricStrategy_wins`, `ChoquetProduct.alphaFavorable_of_completeMetric`, `ChoquetProduct.baireSpace_prod_completeMetric`.

Definition excerpt: `Metric.ediam`. Retained bridge/dependency excerpts: `Metric.ediam`, `Metric.diam`, `PseudoMetricSpace`.

Actual local pinned-toolchain compilation passed for both independent entrypoint modules recorded below. The tests check this literal meaning, class projections/constructor characterization or named proved characterization in its selected-use context; hashes and exact-source comparison remain separate from independent semantic review and protected canonical verification.

## Bridge obligations and evidence limits

The two test files must be built independently through `public import CPChallenge` and `public import CPSolution`; neither module may import both entrypoints. Their material audit blocks check literal definitions, class-field constructor/projection statements and named proved characterizations separately. A class is not definitionally equal to a conjunction of its fields, and the open-intersection meaning of Dense, natural-index meaning of IsGδ, metric Cauchy criterion, and metric boundedness criterion are proved bridges.

The reused BM bridge set supplies topology/open/nonempty/dense/closure/Baire/empty/distinct-label-disjointness meanings. Added obligations cover Gδ, metric and pseudometric fields, exact uniformity/topology compatibility, every-Cauchy-filter completeness, complete sets, Cauchy sequences, convergence, ball inequalities, boundedness/real and extended diameter, and ordinary product topology. Both final test modules compiled in the actual local pinned-toolchain Lake build; their exact digests and the build-log digest are retained in the manifest. Retaining an excerpt alone establishes neither bridge compilation nor protected canonical verification.

The Cantor-intersection dependency requires closed and bounded sets, finite intersections nonempty and real diameters tending to zero. It does not require compact balls. Metric.diam converts the extended supremum using ENNReal.toReal, so its boundedness assumptions are retained and not silently dropped.

Exact Lean-core List/length evidence is retained separately in `CORE-DEFINITIONS.md` and `verification/core-definitions.json`. It does not become Mathlib source merely because the Lean toolchain is required by Mathlib.

## Exact upstream source evidence

### `Mathlib/Topology/Defs/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

Full-file SHA256: `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`. Git blob SHA1: `326105821a5a8ce5041ccf8dce22779bd55fa923`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `topology-open-closed`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

Excerpt SHA256: `32cd02dbee2407d6f2a2709782ad6b65bd88feb3a50558e4951344c640cfafd7`.

```lean
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `X` -/
@[wikidata Q213363]
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen

@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ

theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpace.isOpen_inter s t hs ht

theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h

/-- A set is closed if its complement is open -/
@[wikidata Q320357]
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ


```

#### `interior-closure`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127

Excerpt SHA256: `e08a72b7730b15a59ad60cdbfd00f72b089e1f72279df1dfb1ef9ed8736d0f07`.

```lean
Also see `isLocallyClosed_tfae` and other lemmas in `Mathlib/Topology/LocallyClosed.lean`.
-/
def IsLocallyClosed (s : Set X) : Prop := ∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }

```

#### `Dense`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L145-L147

Excerpt SHA256: `2a52522d35b48a1b96df7fa73b15254b113108436e633e0e45e5bdffc455fbf8`.

```lean
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s

```

#### `BaireSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L235-L240

Excerpt SHA256: `977d5c7b2d9473e369aa9c2df40a2da2bea81bf7fb22f4978096b547f603e335`.

```lean
/-- The property `BaireSpace α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ.
Use `dense_iInter_of_isOpen` which works for any countable index type instead. -/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)

```

#### `TopologicalSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

Excerpt SHA256: `d0b4bb0467136b0769c0f64a370a326acdea032d7609448a0f7d8337b140031f`.

```lean
/-- A topology on `X`. -/
@[to_dual_dont_translate]
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

```

### `Mathlib/Topology/Closure.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean

Full-file SHA256: `d4e49fd0b092d34d5db79261bfc58b69ad3383a113ff2a0f54c0912a8b9afb5c`. Git blob SHA1: `557a4cd1768bc437e6f55fd9635ad07eba7c6080`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `dense_iff_inter_open`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean#L407-L416

Excerpt SHA256: `9a409a04b115c02363949db371f217b2c698b697dc6265202576be7c5de7920f`.

```lean
/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

```

### `Mathlib/Data/Set/Pairwise/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean

Full-file SHA256: `49a08e66f604f22b7978292a7569496c1c69b6e16014aee317ebf9f9750fa6d6`. Git blob SHA1: `fa5e633790a26b7451827cbd834d87dafe1f4f10`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### `PairwiseDisjoint`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean#L250-L258

Excerpt SHA256: `4d382da5fe077b9a61f80db6db72f9596cf47ba580a857100189218aa52ae285`.

```lean

/-- A set is `PairwiseDisjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. We prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former unfolds more
nicely. -/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)

```

### `Mathlib/Logic/Pairwise.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean

Full-file SHA256: `ccac95d1101a308ae38946e81caaa6d2c32e7e90ed99f7305dba9f01a955e62f`. Git blob SHA1: `7a2f0dc7819c5656049e1d99f6ba0be56f1e04ca`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### `Set.Pairwise`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean#L80-L84

Excerpt SHA256: `dc07f59c0a776d37ad78e1161dd9c87ae848c879ee2bdabe152d0a979ac4affa`.

```lean
namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

```

### `Mathlib/Order/Disjoint.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

Full-file SHA256: `5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c`. Git blob SHA1: `7d5339050bb81a9d325ca7536bbe37dba409813f`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### `Disjoint`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L29-L49

Excerpt SHA256: `343e7f81bb0f165ed1d47af17cc8027a7a26b634ca77239d069eb87f9f7e178b`.

```lean
variable {α : Type*}

section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `Inf` would require additional `Decidable`
arguments. -/
@[to_dual /-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implementing `Sup` would require additional `Decidable`
arguments. -/]
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥

```

### `Mathlib/Data/Set/Disjoint.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean

Full-file SHA256: `21e4643bfcae089dbbca262cb9d4b4bad1ad1cd77adf31ae43f4d2f2ab69e492`. Git blob SHA1: `e454989683e886f35bb9d6ef45c429eaadbd0f2d`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
```

#### `set-disjoint`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean#L29-L40

Excerpt SHA256: `16a8ba9d0314facecc723d1659f71529b6cad3dcdb4c213134528acae5f363ab`.

```lean
protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot

@[grind =]
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and

```

### `Mathlib/Data/Set/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

Full-file SHA256: `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`. Git blob SHA1: `866ef6ab673f737a4ffbb7b2138402d5c76e6c05`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

#### `Set.Nonempty`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

Excerpt SHA256: `cb3870fa0008d18792a7122276c41e3e45998a2f2defae575b4225f0a2cf53de`.

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s

```

### `Mathlib/Basic/IsEmpty/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/IsEmpty/Defs.lean

Full-file SHA256: `4cc13389d971b07836334b2c9b2a1d979fa1f0043ea9e37a5ba08a9214765399`. Git blob SHA1: `8cddc87f06c29a7e02b57c48e725d0725febde92`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
```

#### `IsEmpty`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/IsEmpty/Defs.lean#L26-L28

Excerpt SHA256: `91cda3d147caf0690894eb7e775e12d73d277418a3818042a138e40d5cf7579e`.

```lean
/-- `IsEmpty α` expresses that `α` is empty. -/
class IsEmpty (α : Sort u) : Prop where
  protected false : α → False

```

### `Mathlib/Topology/GDelta/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean

Full-file SHA256: `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`. Git blob SHA1: `feae671419368d0d284d9ed57c536b6b54afba33`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

#### `IsGδ`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L62-L64

Excerpt SHA256: `7e136567a7e24bfece5698ef37f33eb8f5cefd4a7610ba8f35c4f9e765917187`.

```lean
/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

```

#### `isGδ_iff_eq_iInter_nat`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L90-L101

Excerpt SHA256: `0e2113073e8539401f878584cd5a9c865b112b247a20ffa4506d3acdf6118a1e`.

```lean
lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n ↦ univ, fun _n ↦ isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf

alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat

```

### `Mathlib/Topology/Constructions/SumProd.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean

Full-file SHA256: `35d6365bebe8c5d331fe01289e857ccc81e6f6392b1f01835d834a35a6931666`. Git blob SHA1: `ff2a20dc397df5309720b3f7c1fdbe83244dfbfc`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

#### `product-topology`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean#L50-L56

Excerpt SHA256: `bf3f7010718cef54196c57b689842a501f33f5fb0d2c152012fd10e8c5fc1f14`.

```lean
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂


```

#### `isOpen_prod_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean#L446-L451

Excerpt SHA256: `363b5c32db26aa3a88d3e6c39a45464b7c42e20d216420ff9c915a59d1b01946`.

```lean
-- TODO: align with `mem_nhds_prod_iff'`
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  isOpen_iff_mem_nhds.trans <| by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]


```

### `Mathlib/Topology/MetricSpace/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

Full-file SHA256: `cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9`. Git blob SHA1: `10910c95e518dfacb8d4fcb88d7e689315791952`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `MetricSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L54-L71

Excerpt SHA256: `5b56d60557f748a59780862ed4ee67767eb50c1e00b5a5ca2fde9be6cdd68c7e`.

```lean
/-- A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
`dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

See pseudometric spaces (`PseudoMetricSpace`) for the similar class with the `dist x y = 0 ↔ x = y`
assumption weakened to `dist x x = 0`.

Any metric space is a T1 topological space and a uniform space (see `TopologicalSpace`, `T1Space`,
`UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[MetricSpace α] [MetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
@[wikidata Q180953]
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

```

### `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

Full-file SHA256: `13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35`. Git blob SHA1: `912bc464320d8ea70f002255c59e9f79d41f6ac2`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Dist`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L100-L108

Excerpt SHA256: `db01a57fd9285c10d2dfa5a5015cf57d0ac68b497028b697181e603289d9fc04`.

```lean

/-- The distance function (given an ambient metric space on `α`), which returns
a real number `dist x y` given `x y : α`. This type class does not enforce non-negativity. -/
@[ext]
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ

export Dist (dist)

```

#### `PseudoMetricSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L124-L153

Excerpt SHA256: `a0d4f299a39e8aa7ba8f7db608e624ed07b23dc5de029b5215d6bed2274daca4`.

```lean
set_option backward.privateInPublic.warn false in
/-- A pseudometric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
reflexivity `dist x x = 0`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

Note that we do not require `dist x y = 0 → x = y`. See metric spaces (`MetricSpace`) for the
similar class with that stronger assumption.

Any pseudometric space is a topological space and a uniform space (see `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudometric space is just a metric space.

We make the uniformity/topology part of the data instead of deriving it from the metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoMetricSpace α] [PseudoMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
class PseudoMetricSpace (α : Type u) : Type u extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  /-- Extended distance between two points -/
  edist : α → α → ℝ≥0∞ := fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ‹_› ‹_› ‹_›))
  edist_dist : ∀ x y : α, edist x y = ENNReal.ofReal (dist x y) := by
    intro x y; exact ENNReal.coe_nnreal_eq _
  toUniformSpace : UniformSpace α := .ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε } := by intros; rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : ℝ, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C } := by intros; rfl

```

#### `Metric.ball`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L368-L375

Excerpt SHA256: `9254e95110ac29f8ddd4f9c3efd54b1c170b0977361801dc39aa766eb7cdf894`.

```lean
/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
@[wikidata Q838611]
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl

```

#### `Metric.closedBall`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L420-L426

Excerpt SHA256: `3597e1d083a212916773e453633c64a0db15ad8d09df6e8af009aa33b3babd61`.

```lean
/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]

```

#### `Metric.isBounded_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L625-L629

Excerpt SHA256: `7dd22941d9b0880008d4085c57ff057daf39d91cab6f6076cfe9ef2873a5eaae`.

```lean
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]


```

#### `Metric.isOpen_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L833-L841

Excerpt SHA256: `2cb15902c148b72cec105db174db8b3cf474f25885869836b8f9bcc319bcc105`.

```lean
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball


```

### `Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

Full-file SHA256: `7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f`. Git blob SHA1: `c2269f217cc1266e8d378b9493c90e1480a0c438`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.cauchy_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L164-L166

Excerpt SHA256: `e6cc78652991cda1494893c83d58219bb9ed712be0d32b10a0a7cfb2f655d56f`.

```lean
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

```

### `Mathlib/Topology/MetricSpace/Cauchy.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

Full-file SHA256: `9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618`. Git blob SHA1: `4f65c04a3aac9896699e53b84846de79031d9836`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.cauchySeq_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean#L53-L61

Excerpt SHA256: `150c559bcbe82b9fde277b6d5bf85fa2ce930c41c31f2d101102126879018242`.

```lean
section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff

```

### `Mathlib/Topology/UniformSpace/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

Full-file SHA256: `0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c`. Git blob SHA1: `3f068a41cafe8605be201dd24b3843bcbba45a6e`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

#### `UniformSpace.Core`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

Excerpt SHA256: `5313987700fb612d91a82f7603e0ae3fe6cda1b5d64773c26afedb74c7f1bb37`.

```lean
/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 SetRel.id ≤ uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity

```

#### `UniformSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L185-L209

Excerpt SHA256: `a67f56908a4cffd4c4c069fff92e9f5256c8d56e81e6c5e074c827feac86bc13`.

```lean
-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
@[wikidata Q652446]
class UniformSpace (α : Type u) extends TopologicalSpace α where
  /-- The uniformity filter. -/
  protected uniformity : Filter (α × α)
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  protected symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  protected comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _

```

### `Mathlib/Topology/UniformSpace/Cauchy.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

Full-file SHA256: `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`. Git blob SHA1: `86640c96b74c3a4161ecae8151f0cdec46f6d64c`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

#### `Cauchy`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33

Excerpt SHA256: `093fba2cb6e2058042cdafb8d2367864e3fec7907ad47cc9288a6509d2c35cc5`.

```lean

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α

```

#### `IsComplete`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L35-L38

Excerpt SHA256: `856f9594a85679ec2725c2c1cfbfe75680d84a66edb8b33aefec8716ba18dd43`.

```lean
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x

```

#### `cauchy_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L47-L53

Excerpt SHA256: `ec670cce44cc90cc9a0d2d516d49bd8f446fe316c14d6dae67921cbc3a4849ae`.

```lean
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

```

#### `CauchySeq`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L184-L188

Excerpt SHA256: `69be93c7d9f789486fca70d690bc417ed6bfc046421efd74ce8cf23535036dc7`.

```lean
/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)

```

#### `CompleteSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373

Excerpt SHA256: `11cb273661eccc126e169d1905a8f37fd8f8d051d7118fa067f22b116b366c75`.

```lean
/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x

```

#### `completeSpace_iff_isComplete_univ`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L407-L412

Excerpt SHA256: `7dd91310d3eccf779c254b58ca90f4f73cf856307fd3ad0894021c9ef38077e1`.

```lean
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩

```

### `Mathlib/Topology/Defs/Filter.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

Full-file SHA256: `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`. Git blob SHA1: `343fd3e5f576a8e0f0f040eb2df8e5c309106655`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `nhds`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

Excerpt SHA256: `50aa67ca57c8473255d83882eea110cc29269ae9a77d58cae57886b24f0bfa07`.

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

```

### `Mathlib/Topology/Neighborhoods.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

Full-file SHA256: `ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a`. Git blob SHA1: `8bfc6cc6c85396ab77a34b0725508d165b3903f4`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `mem_nhds_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256: `3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515`.

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

```

### `Mathlib/Order/Filter/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

Full-file SHA256: `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`. Git blob SHA1: `760285d16af8795fa73313254a28aa651c9d0883`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

Excerpt SHA256: `0d537bbb0e92a3e5a1c9a1c33b713a8c1351c8f23d9b835133dba47b1c526200`.

```lean
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
@[to_dual_dont_translate]
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

```

#### `Filter.order`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L183-L190

Excerpt SHA256: `a99ab18fd794b2e2b76c56bfa8532bcb16e403417f304a87285b776cb5782aca`.

```lean
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl


```

#### `Filter.product`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L444-L452

Excerpt SHA256: `9ef3719fef82cd6404287f98980c3054bbce035b372a7bd938e80fccdc056a78`.

```lean
/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters. -/

```

#### `Filter.principal`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L158

Excerpt SHA256: `b9ac7078f265922dbe9c103f5320642c8b0341f855d674b959a051d39edcee33`.

```lean
/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

@[simp] theorem mem_principal : s ∈ 𝓟 t ↔ t ⊆ s := Iff.rfl


```

#### `Filter.NeBot`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L268-L277

Excerpt SHA256: `1488e11444dcb443471e0955a43cd486caed1add58d2970214794e265e2b9627`.

```lean
/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥

@[push ←]
theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

```

#### `Filter.map-Tendsto`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L405-L423

Excerpt SHA256: `e6f89a53ff1df261c7705955e27a8d227354e5926f369e20b02c35ad98be4313`.

```lean

/-- Unexpander printing `Filter.EventuallySubset l s t` as `s ≤ᶠ[l] t`. -/
@[app_unexpander Filter.EventuallySubset]
meta def unexpandEventuallySubset : Lean.PrettyPrinter.Unexpander
  | `($_ $l $s $t) => `($s ≤ᶠ[$l] $t)
  | _ => throw ()

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx ↦ st hx
  inter_sets hs ht := inter_mem hs ht

/-- `Filter.Tendsto` is the generic "limit of a function" predicate.
  `Tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂

```

#### `Filter.comap`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L425-L439

Excerpt SHA256: `362366ce36802bc59b3b10b58727f2c6636d06fcf2d31241e21f8d26a375d782`.

```lean
/-- The inverse map of a filter. A set `s` belongs to `Filter.comap m f` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ f` such that `m ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `kernImage m s = {y | ∀ x, m x = y → x ∈ s}` belongs to `f`, see `Filter.mem_comap'`.
3. The set `(m '' sᶜ)ᶜ` belongs to `f`, see `Filter.mem_comap_iff_compl` and
   `Filter.compl_mem_comap`.
-/
def comap (m : α → β) (f : Filter β) : Filter α where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩


```

### `Mathlib/Order/Filter/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

Full-file SHA256: `5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb`. Git blob SHA1: `13734fc09a2dff6db46ca52140aceb45d45eccd8`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter.le_principal_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L365-L367

Excerpt SHA256: `d08e61a69841f2db9a4d86aa848cc71575f01b48205811c4cb5515695f163896`.

```lean
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

```

### `Mathlib/Order/Filter/Prod.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

Full-file SHA256: `2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367`. Git blob SHA1: `9ba0b26e290fe850ba43a785d59881ff873a8936`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
```

#### `Filter.mem_prod_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean#L52-L59

Excerpt SHA256: `55010dac263ead057dd2f09e496453866685af85abe7b22563b86eeeef24656c`.

```lean
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h


```

### `Mathlib/Basic/ENNReal/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean

Full-file SHA256: `211629947deb3d78a8541202d33a9fed3d4c8f22215daea3d7d37209a824d947`. Git blob SHA1: `75cadd3fae3f45e1e88abe228266fa115ef5552b`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

#### `ENNReal.toReal_top`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean#L280-L284

Excerpt SHA256: `41e13052a3a2c1ea162c6645a105844897259ede46fbedced3ed26ad0dfc6783`.

```lean
  ext; simp [coe_toNNReal_eq_toReal]

@[simp] theorem toNNReal_top : ∞.toNNReal = 0 := rfl

@[simp] theorem toReal_top : ∞.toReal = 0 := rfl

```

### `Mathlib/Order/Filter/Tendsto.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

Full-file SHA256: `76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce`. Git blob SHA1: `7f85e578caf6eb1d37a45af5203cd059335be9b8`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter.tendsto_def`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean#L31-L33

Excerpt SHA256: `4c72dad4fe0238b5b998a3fbccd5b7f7095b1f6ff3b2d1495b3ab7566d8f0d00`.

```lean
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl

```

### `Mathlib/Order/Filter/AtTopBot/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

Full-file SHA256: `4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621`. Git blob SHA1: `6cf35ed92a409e5acf84c90305ecc7d1dd638619`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```

#### `Filter.atTop`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L29-L40

Excerpt SHA256: `0414b8d5164f9dab4515dade24e8985b274e6226b91ba6e843fbbdd78d40d59b`.

```lean

/-- `atTop` is the filter representing the limit `→ ∞` on an ordered set.
It is generated by the collection of up-sets `{b | a ≤ b}`.
(The preorder need not have a top element for this to be well defined,
and indeed is trivial when a top element `x` exists, i.e., it coincides with `pure x`.) -/
@[to_dual
/-- `atBot` is the filter representing the limit `→ -∞` on an ordered set.
It is generated by the collection of down-sets `{b | b ≤ a}`.
(The preorder need not have a bottom element for this to be well defined,
and indeed is trivial when a bottom element `x` exists, i.e., it coincides with `pure x`.) -/]
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)

```

### `Mathlib/Topology/Bornology/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

Full-file SHA256: `427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e`. Git blob SHA1: `4b142e1d604446eafb9ee39b6a39a492d687c997`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
```

#### `Bornology`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L48-L55

Excerpt SHA256: `6b90100aad31395953206030fe496a5a526e9db1473af7893d4213fc9d139bd8`.

```lean
/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `Bornology.ofBounded`
and `Bornology.ext_iff_isBounded` -/
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded ≤ cofinite

```

#### `Bornology.IsBounded`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L90-L101

Excerpt SHA256: `3acc6f6c18293e7078b7b8ad358957d2614e9bbc7cd2cd8a746687d02d90b51c`.

```lean

section

/-- `IsCobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def IsCobounded [Bornology α] (s : Set α) : Prop :=
  s ∈ cobounded α

/-- `IsBounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def IsBounded [Bornology α] (s : Set α) : Prop :=
  IsCobounded sᶜ


```

### `Mathlib/Topology/MetricSpace/Bounded.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

Full-file SHA256: `dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b`. Git blob SHA1: `b47b2b389eebc08df32ef3a6f450f350c389cfcd`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.diam`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L405-L411

Excerpt SHA256: `6619834688c217d42f16d3c8e78f41e3c88e5181286323b6d8d39411c9d13864`.

```lean
/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the `ediam` -/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (ediam s)

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=

```

#### `Metric.nonempty_iInter_of_nonempty_biInter`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L564-L570

Excerpt SHA256: `17aa72fea3bce982cdc3613292981d760ee2ed9bbb705423938181d1d451ec18`.

```lean
/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'


```

### `Mathlib/Topology/EMetricSpace/Diam.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean

Full-file SHA256: `699ba791a149bdcdc24e9d7d650aa34925e04947d38df7e7c1ef9c9bd195822f`. Git blob SHA1: `d5a39e2f435e837f92a9ed3c804f61d9f6240bbf`. License: Apache-2.0.

Upstream header, unchanged:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.ediam`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean#L24-L34

Excerpt SHA256: `fa87de7eab6b342af268a7e064d1b0518a89b8b9b4f35dc85569dfcd943503bb`.

```lean

namespace Metric

section WeakPseudoEMetricSpace

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam [EDist X] (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]


```

