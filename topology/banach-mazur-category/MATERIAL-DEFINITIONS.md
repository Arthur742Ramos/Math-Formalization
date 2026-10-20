# Pinned material imported-definition audit

This package proves target-set Banach–Mazur determinacy for canonical Baire-property sets in complete metric spaces. It uses an existential target-intersection payoff and actual full-history strategies. The complete-metric conclusions have no separate arbitrary topology, separability, second-countability or nonempty premise. Generic meagre avoidance and residual/open-witness lemmas have their stated weaker hypotheses. The metric construction uses closed bounded shrinking traps, not compactness of closed balls.

This inventory records exact pinned definitions and their dependency expansion. Literal unfolding, class fields and proved equivalences are distinguished below. Every material bridge is represented independently through ChallengeTests and SemanticTests. Source-bound build and review receipts establish which checks completed; hashes alone establish neither successful compilation nor semantic completeness. Exact-source canonical full and renderer reports, browser runtime, current attempts and editorial/registration status have separate scopes.

## Exact dependency

Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55; Lean leanprover/lean4:v4.35.0-rc2. All retained files preserve their Apache-2.0 upstream headers and exact full-file/blob/excerpt hashes. The package lock preserves the same nine dependency pins as Choquet.

## Fixed game semantics and boundaries

OpenMove is an inhabited open subset. FirstStrategy has an initial move at empty history and responds to the entire reverse opponent history. SecondStrategy receives the current first move and the full earlier first history. FollowsFirst/FollowsSecond supply alternating non-strict inclusions. FirstWins asks for one target point in all moves; SecondWins denies such a point. Determined is an actual existential winning-strategy disjunction. Joint-play existence prevents proving incompatible winners through absence of legal histories. An empty ambient type has no initial first move and no infinite opponent move sequence; II-winning statements have the explicitly vacuous empty-domain meaning, and the target is meagre. The BP hypothesis is not silently dropped from the selected iff results.

## `Dense`

Every ambient point belongs to the closure; equivalently every nonempty open set meets the set.

The residual-sequence and avoidance constructions use dense open D n so that every current nonempty open move intersects D n. The openness/intersection characterization is proved by dense_iff_inter_open, not the literal definition. No Baire-space hypothesis is needed to refine a single move; a countable intersection need not be dense in an arbitrary space.

Kind: def; role: hypothesis-and-conclusion; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Dense`. Bridge/dependency excerpts: `Dense`, `dense_iff_inter_open`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `IsOpen`

The open-set predicate supplied by the given ambient topological-space structure.

OpenMove contains precisely an ambient open set with a point. Generic residual-sequence, local-witness and II-avoidance results allow arbitrary topologies. Complete-metric results use the topology inherited from MetricSpace through its compatible uniformity, not an independently arbitrary topology.

Kind: def; role: definition; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.exists_jointPlay`
- `CategoryGame.not_both_winning`
- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `topology-open-closed`. Bridge/dependency excerpts: `topology-open-closed`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `closure`

The intersection of every closed superset of the given set.

IsClosed means the complement is open. Dense is pointwise membership in closure. Nowhere density means empty interior of this closure; no separation or Baire assumption is folded into those predicates.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `interior-closure`. Bridge/dependency excerpts: `interior-closure`, `topology-open-closed`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Set.Nonempty`

There exists one point belonging to the set.

The payoff is (A ∩ ⋂ n, U n).Nonempty: one point must belong to A and every move. It does not assert that every common point lies in A, and a different point for each round is insufficient. An empty ambient type has no OpenMove and no FirstStrategy initial move; II strategy functions have an empty input domain. Joint-play existence obtains its initial legal move from the given FirstStrategy.

Kind: def; role: definition; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.exists_jointPlay`
- `CategoryGame.not_both_winning`
- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Set.Nonempty`. Bridge/dependency excerpts: `Set.Nonempty`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `TopologicalSpace`

An open-set predicate containing the whole space and closed under binary intersections and arbitrary unions.

The generic results use only these open-set axioms. In metric results the inherited topology is constrained by the metric uniformity; there is no extra unrelated TopologicalSpace instance or hidden separability, second-countability, nonemptiness or absence-of-isolated-points premise.

Kind: class; role: definition; bridge: class-fields.

Selected coverage:

- `CategoryGame.exists_jointPlay`
- `CategoryGame.not_both_winning`
- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `TopologicalSpace`. Bridge/dependency excerpts: `TopologicalSpace`, `topology-open-closed`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `MetricSpace`

A real-valued symmetric triangle-inequality distance vanishing exactly when its points are equal, with its compatible topology, uniformity and bornology.

MetricSpace extends PseudoMetricSpace and adds eq_of_dist_eq_zero. PseudoMetricSpace supplies Dist.dist, self-zero, symmetry, triangle inequality, an extended distance compatible with real distance, the uniformity_dist equality and compatible bornology. No completeness, local compactness, properness, separability, or compactness of closed balls follows from this class alone. Metric results use this inherited topology, with no independently arbitrary TopologicalSpace Y.

Kind: class; role: hypothesis; bridge: class-fields.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `MetricSpace`. Bridge/dependency excerpts: `MetricSpace`, `PseudoMetricSpace`, `Dist`, `UniformSpace`, `Metric.isOpen_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `PseudoMetricSpace`

A real-valued pseudometric, its compatible extended distance, uniformity and bornology; zero distance need not separate points.

Class fields require dist_self, dist_comm, dist_triangle; uniformity_dist identifies 𝓤 with the infimum of principal distance-entourages. UniformSpace.nhds_eq_comap_uniformity connects that uniformity to the stored topology. The bornology cobounded_sets field identifies metric bounded sets. These are constraints on stored structures, not an arbitrary topology plus a distance.

Kind: class; role: proof-dependency; bridge: class-fields.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `PseudoMetricSpace`. Bridge/dependency excerpts: `PseudoMetricSpace`, `Dist`, `UniformSpace`, `Metric.isOpen_iff`, `Bornology`, `Metric.isBounded_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `UniformSpace`

A uniformity filter on pairs, symmetric and closed under entourage composition, with compatible stored topology.

The class extends TopologicalSpace and includes symm, comp and nhds_eq_comap_uniformity. Diagonal/reflexivity follows from neighborhood compatibility; it is explicit in the separate Core description. 𝓤 is the uniformity projection. Filter order is reverse inclusion of set collections; nhds denotes all neighborhoods of the current topology.

Kind: class; role: proof-dependency; bridge: class-fields.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `UniformSpace`. Bridge/dependency excerpts: `UniformSpace`, `UniformSpace.Core`, `Filter`, `Filter.principal`, `Filter.map-Tendsto`, `Filter.comap`, `nhds`, `mem_nhds_iff`, `Filter.order`, `Filter.product`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `CompleteSpace`

Every nontrivial Cauchy filter has a limit in the space.

The complete field quantifies all Cauchy filters, not only sequences. Cauchy is NeBot plus f×f≤𝓤; IsComplete univ is proved equivalent. The complete-metric first-player construction applies the pinned closed/bounded finite-intersection diameter-to-zero theorem to explicit traps and thus produces one target point. Empty spaces are permitted: nontrivial Cauchy filters then do not exist. Completeness does not imply compactness of closed balls.

Kind: class; role: hypothesis; bridge: class-fields.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `CompleteSpace`. Bridge/dependency excerpts: `CompleteSpace`, `Cauchy`, `IsComplete`, `completeSpace_iff_isComplete_univ`, `Metric.cauchySeq_iff`, `Metric.nonempty_iInter_of_nonempty_biInter`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Cauchy`

A nontrivial filter whose pairs become arbitrarily uniformly close.

Literal conjunction NeBot f ∧ f×ˢf≤𝓤. NeBot is a separate class asserting f≠⊥; Mathlib filters themselves allow the improper bottom filter. cauchy_iff proves the small-set entourage description, and Metric.cauchy_iff proves its epsilon-distance form. The nontriviality guard is essential to avoid false empty-space limits.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Cauchy`. Bridge/dependency excerpts: `Cauchy`, `cauchy_iff`, `Filter.NeBot`, `Filter`, `Metric.cauchy_iff`, `Filter.order`, `Filter.product`, `Filter.mem_prod_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `IsComplete`

Every Cauchy filter supported on a set has a limit in that same set.

Literally ∀f,Cauchy f→f≤𝓟s→∃x∈s,f≤𝓝x. Principal-filter support means s∈f. The limit belongs to s; mere ambient convergence is insufficient. CompleteSpace is equivalent to IsComplete univ by a proved theorem.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `IsComplete`. Bridge/dependency excerpts: `IsComplete`, `Cauchy`, `Filter.principal`, `nhds`, `completeSpace_iff_isComplete_univ`, `Filter.le_principal_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `CauchySeq`

A map whose image of the atTop filter is Cauchy; for natural-number sequences this is the usual epsilon-tail condition.

The definition supports arbitrary preorders, but the semantic bridge specializes to ℕ: ∀ε>0,∃N,∀m≥N,∀n≥N,dist(a m)(a n)<ε. This is a proved characterization, not the literal defining expression; the latter is Cauchy (Filter.map a atTop). The imported Cantor-intersection theorem uses this completeness infrastructure.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `CauchySeq`. Bridge/dependency excerpts: `CauchySeq`, `Cauchy`, `Filter.atTop`, `Filter.map-Tendsto`, `Metric.cauchySeq_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Filter.Tendsto`

The image filter lies below the target filter: every target-large set has a source-large preimage.

Literally Filter.map f l₁ ≤ l₂. map encodes preimages, and tendsto_def is the equivalent membership form. The shrinking-trap proof uses l₁=atTop on ℕ and l₂=𝓝 0 in ℝ to show the diameters of all late traps tend to zero. This is convergence of the whole sequence, not a subsequence.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Filter.map-Tendsto`. Bridge/dependency excerpts: `Filter.map-Tendsto`, `Filter.tendsto_def`, `Filter.atTop`, `nhds`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Metric.ball`

Points y whose real distance from the center x is strictly less than r.

The first-player strategy chooses a positive-radius open ball inside the current opponent move intersected with the nth dense open D n. Radii are at most (1/2)^history.length. The initial move also refines the prescribed nonempty open region U. This is a fixed proof construction, not a Comparator definition hole.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Metric.ball`. Bridge/dependency excerpts: `Metric.ball`, `MetricSpace`, `PseudoMetricSpace`, `Metric.isOpen_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Metric.closedBall`

Points y whose real distance from the center x is at most r.

A closed trap is chosen inside each legal input. The next closed trap lies in the preceding actual opponent move, which lies in the preceding open ball; hence a common point of the closed traps lies in all actual moves and all D n. Closed traps are bounded and closed; no compactness or properness is assumed.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Metric.closedBall`. Bridge/dependency excerpts: `Metric.closedBall`, `Metric.ball`, `Metric.nonempty_iInter_of_nonempty_biInter`, `Metric.isBounded_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Bornology.IsBounded`

Boundedness in the compatible metric bornology; equivalently all pairwise distances on the set are bounded by some real constant.

Literally IsCobounded of the complement. Bornology stores a cobounded filter, and PseudoMetricSpace.cobounded_sets constrains that filter to the distance bornology. Metric.isBounded_iff is the proved pairwise-distance bound; it is not the literal general bornology definition. Boundedness alone implies neither closedness nor compactness.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Bornology.IsBounded`. Bridge/dependency excerpts: `Bornology.IsBounded`, `Bornology`, `PseudoMetricSpace`, `Metric.isBounded_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Metric.diam`

The real-valued diameter is ENNReal.toReal of the extended diameter.

This definition is not an unconditional finite supremum: ENNReal.toReal maps infinity to zero. Therefore boundedness is material in the credited finite-intersection theorem. Every chosen closed ball is bounded and its real diameter is bounded by twice its radius, so diameter-to-zero is used on finite extended diameters. No unbounded-set or compact-ball claim is made.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Metric.diam`. Bridge/dependency excerpts: `Metric.diam`, `Metric.ediam`, `Metric.nonempty_iInter_of_nonempty_biInter`, `Metric.isBounded_iff`, `ENNReal.toReal_top`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Metric.ediam`

The extended nonnegative diameter is the supremum of edist x y over all x and y in the set.

The supremum ranges over both point-membership proofs and may be infinity. PseudoMetricSpace.edist_dist identifies edist with ENNReal.ofReal of dist. This distinguishes the extended supremum from Metric.diam, which converts to ℝ and sends infinity to zero.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Metric.ediam`. Bridge/dependency excerpts: `Metric.ediam`, `Metric.diam`, `PseudoMetricSpace`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `residual`

The filter of supersets of countable intersections of dense open sets.

The literal filter is Filter.countableGenerate {t | IsOpen t ∧ Dense t}. mem_residual_iff proves the countable-family cover characterization. This need not be a proper filter in a general topological space; do not infer that residual means nonempty or dense without a Baire premise. The selected sequence theorem enumerates a countable family with univ padding; it is valid when the family or ambient space is empty. The local witness uses U ∩ S ⊆ A with S residual globally, rather than asserting A itself is globally residual.

Kind: def; role: hypothesis-and-conclusion; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `residual`. Bridge/dependency excerpts: `residual`, `mem_residual_iff`, `countableInterFilter_residual`, `Filter.countableGenerate`, `Filter.mem_countableGenerate_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `IsMeagre`

The complement belongs to the residual filter; equivalently the set is contained in a countable union of nowhere-dense sets.

The literal definition is sᶜ∈residual X. The countable-nowhere-dense characterization is a proved theorem, not definitional equality. Meagreness is measured in the ambient topology. The main winning-strategy iff results require BaireMeasurableSet A and a complete metric; they do not claim the arbitrary-target converse from their statements.

Kind: def; role: hypothesis-and-conclusion; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `IsMeagre`. Bridge/dependency excerpts: `IsMeagre`, `residual`, `isMeagre_iff_countable_union_isNowhereDense`, `IsNowhereDense`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `IsNowhereDense`

The interior of the closure is empty.

Closure is the intersection of closed supersets and interior is the union of open subsets. The zero interior condition is stronger than merely having empty interior before closure. It gives the category meaning of IsMeagre through the proved countable-union characterization.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `IsNowhereDense`. Bridge/dependency excerpts: `IsNowhereDense`, `interior-closure`, `topology-open-closed`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `BaireMeasurableSet`

The property of Baire: the set differs from an open set by a meagre set.

The literal definition is MeasurableSet for eventuallyMeasurableSpace (borel X) (residual X), equivalently eventual equality modulo residual to some Borel set. borel is the sigma-algebra generated by open sets. The conversion to an OPEN approximating set is the proved BaireMeasurableSet.iff_residualEq_isOpen, together with the eventual pointwise-membership iff and IsMeagre complement definition; it is not definitional equality. No externally supplied MeasurableSpace is used. The selected theorems require this canonical ambient property, not merely arbitrary measurability.

Kind: def; role: hypothesis; bridge: proved-equivalence.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `BaireMeasurableSet`. Bridge/dependency excerpts: `BaireMeasurableSet`, `eventuallyMeasurableSpace`, `EventuallyMeasurableSet`, `borel`, `MeasurableSet`, `MeasurableSpace`, `GenerateMeasurable`, `generateFrom`, `BaireMeasurableSet.iff_residualEq_isOpen`, `BaireMeasurableSet.residualEq_isOpen`, `Filter.eventuallyEqSet_iff`, `Filter.EventuallyEqSet`, `Filter.EventuallyEq`, `residual`, `IsMeagre`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `MeasurableSet`

Membership in the sigma-algebra stored in the given MeasurableSpace.

MeasurableSpace is a record with a set predicate closed under empty set, complements and natural-number unions. MeasurableSet projects that record predicate. In BaireMeasurableSet the supplied record is explicitly eventuallyMeasurableSpace (borel X) (residual X); it is not an arbitrary ambient measure or sigma-algebra.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `MeasurableSet`. Bridge/dependency excerpts: `MeasurableSet`, `MeasurableSpace`, `eventuallyMeasurableSpace`, `borel`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `MeasurableSpace.generateFrom`

The least sigma-algebra generated by a specified family of basic sets.

The record predicate is the inductive GenerateMeasurable, with basic, empty, complement and natural-number-union constructors. Taking the basic family to be all ambient open sets gives borel. No measure, numerical value or completion by null sets occurs.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `generateFrom`. Bridge/dependency excerpts: `generateFrom`, `GenerateMeasurable`, `MeasurableSpace`, `MeasurableSet`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `borel`

The sigma-algebra generated by the ambient open sets.

Literally MeasurableSpace.generateFrom {s | IsOpen s}. These Borel sets supply the initial sigma-algebra in the canonical Baire-property definition. The open approximation used to construct a winning strategy is a proved regularity theorem for the residual ideal; it does not identify Borel sets with open sets.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `borel`. Bridge/dependency excerpts: `borel`, `generateFrom`, `GenerateMeasurable`, `topology-open-closed`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `eventuallyMeasurableSpace`

The sigma-algebra of sets eventually equal to a measurable set along a countably intersection-closed filter.

Its measurable predicate is ∃t, MeasurableSet t ∧ s =ᶠ[l] t. The filter hypothesis is CountableInterFilter l, which permits combining countably many eventual equalities; residual X carries that instance. A Baire-property set therefore agrees pointwise in membership with a Borel set off a meagre exceptional set.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `eventuallyMeasurableSpace`. Bridge/dependency excerpts: `eventuallyMeasurableSpace`, `eventuallyMeasurableSpace.parameters`, `MeasurableSet`, `Filter.EventuallyEqSet`, `Filter.EventuallyEq`, `Filter.eventuallyEqSet_iff`, `residual`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `EventuallyMeasurableSet`

Measurability in the sigma-algebra eventuallyMeasurableSpace.

This wraps the measurable-set predicate of the constructed sigma-algebra, so it unfolds to the same existence of a base-measurable set with eventual membership equality. BaireMeasurableSet chooses the canonical Borel base and residual filter.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `EventuallyMeasurableSet`. Bridge/dependency excerpts: `EventuallyMeasurableSet`, `eventuallyMeasurableSpace`, `MeasurableSet`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Filter.EventuallyEq`

Equality holds on a set belonging to the given filter.

The literal body is ∀ᶠx in l, f x = g x; Filter.Eventually is set membership in l. For characteristic propositions the statement that membership propositions are equal is equivalent to membership iff. Filters may be improper; this is not an assertion of dense or nonempty coincidence in arbitrary spaces.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Filter.EventuallyEq`. Bridge/dependency excerpts: `Filter.EventuallyEq`, `Filter.Eventually`, `Filter`, `Filter.eventuallyEqSet_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Filter.EventuallyEqSet`

The two set-membership predicates agree eventually along the specified filter.

This is EventuallyEq applied to x↦x∈s and x↦x∈t. Filter.eventuallyEqSet_iff proves the eventual pointwise iff form used in the open witness. Equality of propositions and iff are not silently conflated as a definitional rewrite.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Filter.EventuallyEqSet`. Bridge/dependency excerpts: `Filter.EventuallyEqSet`, `Filter.EventuallyEq`, `Filter.Eventually`, `Filter.eventuallyEqSet_iff`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `CountableInterFilter`

The filter is closed under intersections of countable families of its sets.

The class field quantifies every countable Set (Set X) whose members belong to l and puts its full intersection back in l. The condition allows the empty family and does not imply that the filter is proper. residual X gets this structure from countableGenerate; it permits the eventual-measurability sigma-algebra to close under countable unions.

Kind: class; role: proof-dependency; bridge: class-fields.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `CountableInterFilter`. Bridge/dependency excerpts: `CountableInterFilter`, `Filter.countableGenerate`, `Filter.CountableGenerateSets`, `Filter.ofCountableInter`, `Filter.mem_countableGenerate_iff`, `countableInterFilter_residual`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Filter.countableGenerate`

The countably intersection-closed filter generated by a collection of basic sets.

CountableGenerateSets closes the basic family under univ, supersets and countable intersections; ofCountableInter packages these sets as a filter. Its membership characterization is proved: a member contains a countable intersection of basic sets. residual specializes those basics to ambient dense open sets. No nonemptiness assumption is introduced by this generated-filter definition.

Kind: def; role: proof-dependency; bridge: proved-equivalence.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Filter.countableGenerate`. Bridge/dependency excerpts: `Filter.countableGenerate`, `Filter.CountableGenerateSets`, `Filter.ofCountableInter`, `Filter.mem_countableGenerate_iff`, `CountableInterFilter`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Countable`

There exists an injection from the type into the natural numbers.

The Countable existence-of-injective-map field permits finite and empty types, with no required surjection from naturals onto an empty type. This is the underlying cardinal meaning of the countable families in residual, sigma-algebra closure and generated filters.

Kind: class; role: proof-dependency; bridge: class-fields.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Countable`. Bridge/dependency excerpts: `Countable`, `Set.Countable`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## `Set.Countable`

The subtype of elements of the set is countable.

Literally Countable s for the membership subtype s. Therefore a countable family of open sets need not be inhabited; the residual-sequence proof pads its enumeration by univ. This is distinct from choosing an element of an assumed nonempty family.

Kind: def; role: proof-dependency; bridge: literal-unfolding.

Selected coverage:

- `CategoryGame.residual_has_dense_open_sequence`
- `CategoryGame.second_winning_of_isMeagre`
- `CategoryGame.open_residual_witness`
- `CategoryGame.first_winning_of_open_residual`
- `CategoryGame.first_winning_of_nonmeagre`
- `CategoryGame.determined_of_baireMeasurable`
- `CategoryGame.first_winning_iff_nonmeagre`
- `CategoryGame.second_winning_iff_isMeagre`

Exact defining excerpt: `Set.Countable`. Bridge/dependency excerpts: `Set.Countable`, `Countable`.

Both independent entrypoint modules retain the literal/class-field/proved bridges listed here. Actual source-bound Lean build receipts establish their compilation; hashes and retained excerpts establish neither compilation nor inventory completeness. Independent mathematical/source review assesses completeness and use-specific fidelity. Canonical full comparison and rendering have separate exact-source receipts.

## Retained exact source files and excerpts

### `Mathlib/Topology/Defs/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

Full-file SHA256 `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`; Git blob `326105821a5a8ce5041ccf8dce22779bd55fa923`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `topology-open-closed`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

Excerpt SHA256 `32cd02dbee2407d6f2a2709782ad6b65bd88feb3a50558e4951344c640cfafd7`.

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

Excerpt SHA256 `e08a72b7730b15a59ad60cdbfd00f72b089e1f72279df1dfb1ef9ed8736d0f07`.

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

Excerpt SHA256 `2a52522d35b48a1b96df7fa73b15254b113108436e633e0e45e5bdffc455fbf8`.

```lean
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

#### `TopologicalSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

Excerpt SHA256 `d0b4bb0467136b0769c0f64a370a326acdea032d7609448a0f7d8337b140031f`.

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

Full-file SHA256 `d4e49fd0b092d34d5db79261bfc58b69ad3383a113ff2a0f54c0912a8b9afb5c`; Git blob `557a4cd1768bc437e6f55fd9635ad07eba7c6080`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `dense_iff_inter_open`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean#L407-L416

Excerpt SHA256 `9a409a04b115c02363949db371f217b2c698b697dc6265202576be7c5de7920f`.

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

### `Mathlib/Data/Set/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

Full-file SHA256 `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`; Git blob `866ef6ab673f737a4ffbb7b2138402d5c76e6c05`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

#### `Set.Nonempty`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

Excerpt SHA256 `cb3870fa0008d18792a7122276c41e3e45998a2f2defae575b4225f0a2cf53de`.

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
```

### `Mathlib/Topology/MetricSpace/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

Full-file SHA256 `cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9`; Git blob `10910c95e518dfacb8d4fcb88d7e689315791952`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `MetricSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L54-L71

Excerpt SHA256 `5b56d60557f748a59780862ed4ee67767eb50c1e00b5a5ca2fde9be6cdd68c7e`.

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

Full-file SHA256 `13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35`; Git blob `912bc464320d8ea70f002255c59e9f79d41f6ac2`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Dist`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L100-L108

Excerpt SHA256 `db01a57fd9285c10d2dfa5a5015cf57d0ac68b497028b697181e603289d9fc04`.

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

Excerpt SHA256 `a0d4f299a39e8aa7ba8f7db608e624ed07b23dc5de029b5215d6bed2274daca4`.

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

Excerpt SHA256 `9254e95110ac29f8ddd4f9c3efd54b1c170b0977361801dc39aa766eb7cdf894`.

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

Excerpt SHA256 `3597e1d083a212916773e453633c64a0db15ad8d09df6e8af009aa33b3babd61`.

```lean
/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]
```

#### `Metric.isBounded_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L625-L629

Excerpt SHA256 `7dd22941d9b0880008d4085c57ff057daf39d91cab6f6076cfe9ef2873a5eaae`.

```lean
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]

```

#### `Metric.isOpen_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L833-L841

Excerpt SHA256 `2cb15902c148b72cec105db174db8b3cf474f25885869836b8f9bcc319bcc105`.

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

Full-file SHA256 `7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f`; Git blob `c2269f217cc1266e8d378b9493c90e1480a0c438`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.cauchy_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L164-L166

Excerpt SHA256 `e6cc78652991cda1494893c83d58219bb9ed712be0d32b10a0a7cfb2f655d56f`.

```lean
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff
```

### `Mathlib/Topology/MetricSpace/Cauchy.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

Full-file SHA256 `9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618`; Git blob `4f65c04a3aac9896699e53b84846de79031d9836`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.cauchySeq_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean#L53-L61

Excerpt SHA256 `150c559bcbe82b9fde277b6d5bf85fa2ce930c41c31f2d101102126879018242`.

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

Full-file SHA256 `0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c`; Git blob `3f068a41cafe8605be201dd24b3843bcbba45a6e`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

#### `UniformSpace.Core`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

Excerpt SHA256 `5313987700fb612d91a82f7603e0ae3fe6cda1b5d64773c26afedb74c7f1bb37`.

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

Excerpt SHA256 `a67f56908a4cffd4c4c069fff92e9f5256c8d56e81e6c5e074c827feac86bc13`.

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

Full-file SHA256 `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`; Git blob `86640c96b74c3a4161ecae8151f0cdec46f6d64c`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

#### `Cauchy`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33

Excerpt SHA256 `093fba2cb6e2058042cdafb8d2367864e3fec7907ad47cc9288a6509d2c35cc5`.

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

Excerpt SHA256 `856f9594a85679ec2725c2c1cfbfe75680d84a66edb8b33aefec8716ba18dd43`.

```lean
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
```

#### `cauchy_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L47-L53

Excerpt SHA256 `ec670cce44cc90cc9a0d2d516d49bd8f446fe316c14d6dae67921cbc3a4849ae`.

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

Excerpt SHA256 `69be93c7d9f789486fca70d690bc417ed6bfc046421efd74ce8cf23535036dc7`.

```lean
/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)
```

#### `CompleteSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373

Excerpt SHA256 `11cb273661eccc126e169d1905a8f37fd8f8d051d7118fa067f22b116b366c75`.

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

Excerpt SHA256 `7dd91310d3eccf779c254b58ca90f4f73cf856307fd3ad0894021c9ef38077e1`.

```lean
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩
```

### `Mathlib/Topology/Defs/Filter.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

Full-file SHA256 `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`; Git blob `343fd3e5f576a8e0f0f040eb2df8e5c309106655`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `nhds`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

Excerpt SHA256 `50aa67ca57c8473255d83882eea110cc29269ae9a77d58cae57886b24f0bfa07`.

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

Full-file SHA256 `ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a`; Git blob `8bfc6cc6c85396ab77a34b0725508d165b3903f4`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### `mem_nhds_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256 `3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515`.

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
```

### `Mathlib/Order/Filter/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

Full-file SHA256 `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`; Git blob `760285d16af8795fa73313254a28aa651c9d0883`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

Excerpt SHA256 `0d537bbb0e92a3e5a1c9a1c33b713a8c1351c8f23d9b835133dba47b1c526200`.

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

Excerpt SHA256 `a99ab18fd794b2e2b76c56bfa8532bcb16e403417f304a87285b776cb5782aca`.

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

Excerpt SHA256 `9ef3719fef82cd6404287f98980c3054bbce035b372a7bd938e80fccdc056a78`.

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

Excerpt SHA256 `b9ac7078f265922dbe9c103f5320642c8b0341f855d674b959a051d39edcee33`.

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

Excerpt SHA256 `1488e11444dcb443471e0955a43cd486caed1add58d2970214794e265e2b9627`.

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

Excerpt SHA256 `e6f89a53ff1df261c7705955e27a8d227354e5926f369e20b02c35ad98be4313`.

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

Excerpt SHA256 `362366ce36802bc59b3b10b58727f2c6636d06fcf2d31241e21f8d26a375d782`.

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

#### `Filter.Eventually`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L279-L282

Excerpt SHA256 `8e168086074ed684a9190fa9b4baaf1df88627836ea57029e867c4b57235e6cb`.

```lean
/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
```

#### `Filter.EventuallyEq`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L297-L298

Excerpt SHA256 `61f15334829664f117f584f561918ffe0abfd3c4f0cc2cb9019b9460934c28c6`.

```lean
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x
```

#### `Filter.EventuallyEqSet`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L310-L311

Excerpt SHA256 `97de9f934919f315a0620741dbe041f601407287fd37ae506edc3583e23524d1`.

```lean
def EventuallyEqSet (l : Filter α) (s t : Set α) : Prop :=
  EventuallyEq l (fun x => x ∈ s) (fun x => x ∈ t)
```

### `Mathlib/Order/Filter/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

Full-file SHA256 `5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb`; Git blob `13734fc09a2dff6db46ca52140aceb45d45eccd8`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter.le_principal_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L365-L367

Excerpt SHA256 `d08e61a69841f2db9a4d86aa848cc71575f01b48205811c4cb5515695f163896`.

```lean
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩
```

#### `Filter.eventuallyEqSet_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L943-L944

Excerpt SHA256 `43edcbeb206718a9a3594bed01ef56e2bdf19221acfb9f902b0b68940458c9e2`.

```lean
theorem eventuallyEqSet_iff {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| Eventually.of_forall fun _ ↦ eq_iff_iff
```

### `Mathlib/Order/Filter/Prod.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

Full-file SHA256 `2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367`; Git blob `9ba0b26e290fe850ba43a785d59881ff873a8936`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
```

#### `Filter.mem_prod_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean#L52-L59

Excerpt SHA256 `55010dac263ead057dd2f09e496453866685af85abe7b22563b86eeeef24656c`.

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

Full-file SHA256 `211629947deb3d78a8541202d33a9fed3d4c8f22215daea3d7d37209a824d947`; Git blob `75cadd3fae3f45e1e88abe228266fa115ef5552b`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

#### `ENNReal.toReal_top`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean#L280-L284

Excerpt SHA256 `41e13052a3a2c1ea162c6645a105844897259ede46fbedced3ed26ad0dfc6783`.

```lean
  ext; simp [coe_toNNReal_eq_toReal]

@[simp] theorem toNNReal_top : ∞.toNNReal = 0 := rfl

@[simp] theorem toReal_top : ∞.toReal = 0 := rfl
```

### `Mathlib/Order/Filter/Tendsto.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

Full-file SHA256 `76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce`; Git blob `7f85e578caf6eb1d37a45af5203cd059335be9b8`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

#### `Filter.tendsto_def`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean#L31-L33

Excerpt SHA256 `4c72dad4fe0238b5b998a3fbccd5b7f7095b1f6ff3b2d1495b3ab7566d8f0d00`.

```lean
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
```

### `Mathlib/Order/Filter/AtTopBot/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

Full-file SHA256 `4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621`; Git blob `6cf35ed92a409e5acf84c90305ecc7d1dd638619`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```

#### `Filter.atTop`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L29-L40

Excerpt SHA256 `0414b8d5164f9dab4515dade24e8985b274e6226b91ba6e843fbbdd78d40d59b`.

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

Full-file SHA256 `427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e`; Git blob `4b142e1d604446eafb9ee39b6a39a492d687c997`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
```

#### `Bornology`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L48-L55

Excerpt SHA256 `6b90100aad31395953206030fe496a5a526e9db1473af7893d4213fc9d139bd8`.

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

Excerpt SHA256 `3acc6f6c18293e7078b7b8ad358957d2614e9bbc7cd2cd8a746687d02d90b51c`.

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

Full-file SHA256 `dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b`; Git blob `b47b2b389eebc08df32ef3a6f450f350c389cfcd`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.diam`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L405-L411

Excerpt SHA256 `6619834688c217d42f16d3c8e78f41e3c88e5181286323b6d8d39411c9d13864`.

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

Excerpt SHA256 `17aa72fea3bce982cdc3613292981d760ee2ed9bbb705423938181d1d451ec18`.

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

Full-file SHA256 `699ba791a149bdcdc24e9d7d650aa34925e04947d38df7e7c1ef9c9bd195822f`; Git blob `d5a39e2f435e837f92a9ed3c804f61d9f6240bbf`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

#### `Metric.ediam`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean#L24-L34

Excerpt SHA256 `fa87de7eab6b342af268a7e064d1b0518a89b8b9b4f35dc85569dfcd943503bb`.

```lean

namespace Metric

section WeakPseudoEMetricSpace

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam [EDist X] (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]

```

### `Mathlib/Topology/Baire/BaireMeasurable.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean

Full-file SHA256 `bbffc3a9d1c907719cfce15eced5d4e2fa8214a878c6d42d8ccbecfeb40d2aee`; Git blob `fc445a39538cd7275e52fc6b2efc1321a4e2681b`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
```

#### `residual-equality-notation`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L36-L40

Excerpt SHA256 `8cc1d8589867d264789893aff893d03794954d6c09962f94c852d355d1bd25a8`.

```lean
/-- Notation for `=ᶠ[residual _]`. That is, eventual equality with respect to
the filter of residual sets.
In lemma names, this is called `residualEq`. -/
scoped[Topology] notation:50 f " =ᵇ " g:50 => f =ᶠ[residual _] g

```

#### `BaireMeasurableSet`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L86-L92

Excerpt SHA256 `d46e7e4d6fc517617dfb59a70c015d7ee5d4e3daf7ed4dbd20e19b7dc09ac60c`.

```lean
/-- We say a set is a `BaireMeasurableSet` if it differs from some Borel set by
a meager set. This forms a σ-algebra.

It is equivalent, and a more standard definition, to say that the set differs from
some *open* set by a meager set. See `BaireMeasurableSet.iff_residualEq_isOpen` -/
def BaireMeasurableSet (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace (borel _) (residual _)) s
```

#### `BaireMeasurableSet.compl`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L110-L110

Excerpt SHA256 `110a7c0a4c42628df2a6b6ac89f43003f19945fd5b734482bc9bb8e80481d057`.

```lean
theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h
```

#### `MeasurableSet.residualEq_isOpen`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L160-L171

Excerpt SHA256 `40a6fb606b2663c7f55dba5fcb15918d5250846a6a69cec7e30b2271b61185d2`.

```lean
/-- Any Borel set differs from some open set by a meager set. -/
theorem MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    ∃ u : Set α, IsOpen u ∧ s =ᵇ u := by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
    exact .compl <| hsU.trans <| .symm <| closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
    choose u uo su using ihf
    exact ⟨⋃ i, u i, isOpen_iUnion uo, .countable_iUnion su⟩
```

#### `BaireMeasurableSet.residualEq_isOpen`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L173-L179

Excerpt SHA256 `c0e0de2b6ca13e7d1b60a007eb38cf8dd847ad5c8f1aeec5660ff632950c4be1`.

```lean
/-- Any `BaireMeasurableSet` differs from some open set by a meager set. -/
theorem BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩
```

#### `BaireMeasurableSet.iff_residualEq_isOpen`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Baire/BaireMeasurable.lean#L181-L184

Excerpt SHA256 `59045f45a55a1cb853ac712369f0190aee781db23657f8f333af1f7f0bc758c0`.

```lean
/-- A set is Baire measurable if and only if it differs from some open set by a meager set. -/
theorem BaireMeasurableSet.iff_residualEq_isOpen :
    BaireMeasurableSet s ↔ ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u :=
  ⟨fun h => h.residualEq_isOpen, fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩
```

### `Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean

Full-file SHA256 `30a9186a18255b552b2f616c00632506cfb999a5518dfd8671d3fbcc5a7dcd10`; Git blob `1bd69126fbae107fc4b6bde6a8a9673d146901ce`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
```

#### `eventuallyMeasurableSpace.parameters`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean#L37-L39

Excerpt SHA256 `2184e965fda03872b0f8c3412178d525a785f1ba033666c0eff86d40ff8920e7`.

```lean
open Filter Set MeasurableSpace

variable {α : Type*} (m : MeasurableSpace α) {s t : Set α}
```

#### `eventuallyMeasurableSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean#L41-L51

Excerpt SHA256 `e3bd4d3edf2ae652f88f85e610ccef2f9ac47c8c321d2430cd2b344954301c55`.

```lean
/-- The `MeasurableSpace` of sets which are measurable with respect to a given σ-algebra `m`
on `α`, modulo a given σ-filter `l` on `α`. -/
@[instance_reducible]
def eventuallyMeasurableSpace (l : Filter α) [CountableInterFilter l] : MeasurableSpace α where
  MeasurableSet' s := ∃ t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, .countable_iUnion hts⟩

```

#### `EventuallyMeasurableSet`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/EventuallyMeasurable.lean#L52-L56

Excerpt SHA256 `add3b56d85c866bb3375d187e2bbb071670328270ab734dcc4ab81fad87924ee`.

```lean
/-- We say a set `s` is an `EventuallyMeasurableSet` with respect to a given
σ-algebra `m` and σ-filter `l` if it differs from a set in `m` by a set in
the dual ideal of `l`. -/
def EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l] (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace m l) s
```

### `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean

Full-file SHA256 `d15ab5af19662b4cd2ae3c3a9665ae52e134d8954ad17d5ded063819b72b7e40`; Git blob `7c7da67bdb2729e65b1245a11c800f945ee6214e`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

#### `borel`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean#L49-L52

Excerpt SHA256 `cd3b12ae1b04f23006d4af175f3528f60b5f5483b805609aa0e1b13bb11c7df2`.

```lean
/-- `MeasurableSpace` structure generated by `TopologicalSpace`. -/
@[instance_reducible]
def borel (α : Type u) [TopologicalSpace α] : MeasurableSpace α :=
  generateFrom { s : Set α | IsOpen s }
```

### `Mathlib/Topology/GDelta/Basic.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean

Full-file SHA256 `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`; Git blob `feae671419368d0d284d9ed57c536b6b54afba33`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

#### `residual`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L169-L174

Excerpt SHA256 `40511e662d43c822959d4d5eb99bb2eb56e8060e02b748a622b553f1b6c5d4f9`.

```lean
/-- A set `s` is called *residual* if it includes a countable intersection of dense open sets. -/
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }

instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance
```

#### `mem_residual_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L187-L192

Excerpt SHA256 `a6efd3171b43b5a21cb8b5320db08dfaf9b997326bfeb2fb19079975c84275f8`.

```lean
/-- A set is residual iff it includes a countable intersection of dense open sets. -/
theorem mem_residual_iff {s : Set X} :
    s ∈ residual X ↔
      ∃ S : Set (Set X), (∀ t ∈ S, IsOpen t) ∧ (∀ t ∈ S, Dense t) ∧ S.Countable ∧ ⋂₀ S ⊆ s :=
  mem_countableGenerate_iff.trans <| by simp_rw [subset_def, mem_ofPred, forall_and, and_assoc]

```

#### `IsNowhereDense`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L199-L200

Excerpt SHA256 `c1e6842368a7dcba1a45a74552e1bf5c7c110ca6660cb7ec07cd88797a612880`.

```lean
/-- A set is called **nowhere dense** iff its closure has empty interior. -/
def IsNowhereDense (s : Set X) := interior (closure s) = ∅
```

#### `IsMeagre`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L283-L284

Excerpt SHA256 `80d5ad65363710a540b6617b2f76c42436ad82097aa65a8f085b262cfdc163cd`.

```lean
/-- A set is called **meagre** iff its complement is a residual (or comeagre) set. -/
def IsMeagre (s : Set X) := sᶜ ∈ residual X
```

#### `isMeagre_iff_countable_union_isNowhereDense`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L319-L331

Excerpt SHA256 `8306417c06ff75de6556ecd914205dab74740cfd3a2f8ffe9d4b727560cc2b7b`.

```lean
/-- A set is meagre iff it is contained in a countable union of nowhere dense sets. -/
lemma isMeagre_iff_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ ∃ S : Set (Set X), (∀ t ∈ S, IsNowhereDense t) ∧ S.Countable ∧ s ⊆ ⋃₀ S := by
  rw [IsMeagre, mem_residual_iff, compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS, hc, hsub⟩ ↦ ⟨S, fun s hs ↦ (hS hs).2, ?_, hsub⟩, ?_⟩
  · rw [← compl_compl_image S]; exact hc.image _
  · intro ⟨S, hS, hc, hsub⟩
    use closure '' S
    rw [forall_mem_image]
    exact ⟨fun s hs ↦ ⟨isClosed_closure, (hS s hs).closure⟩,
      (hc.image _).image _, hsub.trans (sUnion_mono_subsets fun s ↦ subset_closure)⟩
```

#### `countableInterFilter_residual`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L173-L174

Excerpt SHA256 `90d6a47baf82c8ba1a7b751378a659eb8d5aa2e11f374b01fb245b70e999e76b`.

```lean
instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance
```

### `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean

Full-file SHA256 `ab0d3d10d1376174984380238dbe86a963be068fe78c665dd6729cc52fa37ac4`; Git blob `cf508919f298fd7b7dcfe36f09c02dc108d579c9`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

#### `MeasurableSpace`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean#L49-L60

Excerpt SHA256 `c033aaf3b7567a50eaeecb1b5d39ba13293d884136722905eed140ed6e550d3b`.

```lean
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)

```

#### `MeasurableSet`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean#L64-L65

Excerpt SHA256 `1ae22591f7271843e8e6f0b1b9c0fe21c24e3f3465179a9cd1f0930831b7027a`.

```lean
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s
```

#### `GenerateMeasurable`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean#L321-L327

Excerpt SHA256 `98ba6f4d10d1e6e4709b9a021a5874fda54d055ba2ca12a46e840d432e94df0c`.

```lean
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | protected basic : ∀ u ∈ s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | protected iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)

```

#### `generateFrom`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean#L330-L334

Excerpt SHA256 `a60487a1cd6b78042bcd7d0535bfd58ffb7ad7aaa5846c0e5dad77961d0fcee5`.

```lean
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion
```

### `Mathlib/Order/Filter/CountableInter.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean

Full-file SHA256 `b6854464b88925956362116ea97e5e427b6955f99ab714d32900a15e00c230fd`; Git blob `e23749c7d2e55ce5ed83a21b279237a700d20a54`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

#### `CountableInterFilter`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L42-L44

Excerpt SHA256 `44b7bd0fac0b6bfe6b45ca4b2b7d3288e7393e3b5579fb69b8ffaa735f81c64e`.

```lean
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l
```

#### `Filter.CountableGenerateSets`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L272-L277

Excerpt SHA256 `ec7ca973d1f36ca5d22efb8b061544d0281dc27e031826284c1ef2b25e685268`.

```lean
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
```

#### `Filter.countableGenerate`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L281-L283

Excerpt SHA256 `89645c75f7deb78e4554be2929811f05679596397e24f2aa1e915787cbc332a3`.

```lean
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ ↦ .sInter) fun _ _ ↦ .superset
deriving CountableInterFilter
```

#### `Filter.mem_countableGenerate_iff`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L289-L305

Excerpt SHA256 `e0d3509f8fac3e9e85dbc79d320898d9f852d3256c3f01d48615947797912677`.

```lean
theorem mem_countableGenerate_iff {s : Set α} :
    s ∈ countableGenerate g ↔ ∃ S : Set (Set α), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs => exact ⟨{s}, by simp [hs]⟩
    | univ => exact ⟨∅, by simp⟩
    | superset _ _ ih => refine Exists.imp (fun S => ?_) ih; tauto
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, Sct.biUnion Tct, ?_⟩
      apply subset_sInter
      intro s H
      exact subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine mem_of_superset ((countable_sInter_mem Sct).mpr ?_) hS
  intro s H
  exact CountableGenerateSets.basic (Sg H)
```

#### `Filter.ofCountableInter`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L166-L173

Excerpt SHA256 `036aff58055fd3a9a2b02d1bbd9c5e25c308306ea4b271d584a4ee4dcab1d8e1`.

```lean
def ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
```

### `Mathlib/Basic/Countable/Defs.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

Full-file SHA256 `d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f`; Git blob `2718dae9396dc0acff5f8b703d3587512b0281db`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

#### `Countable`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41-L46

Excerpt SHA256 `551b5558571ec8d95682ed77589bddacda46501f10be4eef3efb6971e2a241e9`.

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'
```

### `Mathlib/Data/Set/Countable.lean`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

Full-file SHA256 `047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98`; Git blob `f5ffd2035308f61e38f10aad4df99b2405ec519a`; license Apache-2.0.

Upstream attribution:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### `Set.Countable`

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L40-L49

Excerpt SHA256 `029b5880e2f8d6ee503311ecdcfba5d91268eceeb5194b1788413175bcb3ccd5`.

```lean
namespace Set

/-- A set `s` is countable if the corresponding subtype is countable,
i.e., there exists an injective map `f : s → ℕ`.

Note that this is an abbreviation, so `hs : Set.Countable s` in the proof context
is the same as an instance `Countable s`.
For a constructive version, see `Encodable`.
-/
protected def Countable (s : Set α) : Prop := Countable s
```

