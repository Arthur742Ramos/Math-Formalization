# Material imported meanings

This inventory includes the full prior foundation dependency expansion and new image hypotheses. It does not certify editorial suitability.

Selected contracts: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Dense

Every point belongs to the closure.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The separable-space completion chain uses a countable dense subset. The canonical completion map has dense range, but the image itself need not be closed or complete for the original metric.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsOpen

The open predicate of the given ambient topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Moves and replies are ambient opens; the selected marked point belongs to each reply. Generic legal-play and empty-space results need only a topology. Metric results inherit exactly the compatible metric topology; the main converse additionally assumes second countability and metrizability.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## closure

The intersection of all closed supersets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Closure and Dense explain the separability instance chain. The converse proves the actual source image is Gδ, not just that its closure is the complete ambient.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Set.Nonempty

There exists a point in the set.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Winning requires one common point in every reply, not a different point each round. Legal plays have equal first-move and reply intersections. Empty spaces have no Move; the actual empty-domain Strategy is winning vacuously, explicitly proved.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## TopologicalSpace

An open-set predicate containing the universe, closed under binary intersection and arbitrary union.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Second-countable metrizable results preserve this exact topology when a complete metric is chosen. There is no extra arbitrary topology in metric statements. Empty and isolated points are allowed.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## MetricSpace

A real-valued symmetric triangle-inequality distance vanishing exactly when its points are equal, with its compatible topology, uniformity and bornology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. MetricSpace extends PseudoMetricSpace and adds eq_of_dist_eq_zero. PseudoMetricSpace supplies Dist.dist, self-zero, symmetry, triangle inequality, an extended distance compatible with real distance, the uniformity_dist equality and compatible bornology. No completeness, local compactness, properness, separability, or compactness of closed balls follows from this class alone. Metric results use this inherited topology, with no independently arbitrary TopologicalSpace Y. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## PseudoMetricSpace

A real-valued pseudometric, its compatible extended distance, uniformity and bornology; zero distance need not separate points.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Class fields require dist_self, dist_comm, dist_triangle; uniformity_dist identifies 𝓤 with the infimum of principal distance-entourages. UniformSpace.nhds_eq_comap_uniformity connects that uniformity to the stored topology. The bornology cobounded_sets field identifies metric bounded sets. These are constraints on stored structures, not an arbitrary topology plus a distance. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## UniformSpace

A uniformity filter on pairs, symmetric and closed under entourage composition, with compatible stored topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The class extends TopologicalSpace and includes symm, comp and nhds_eq_comap_uniformity. Diagonal/reflexivity follows from neighborhood compatibility; it is explicit in the separate Core description. 𝓤 is the uniformity projection. Filter order is reverse inclusion of set collections; nhds denotes all neighborhoods of the current topology. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## CompleteSpace

Every Cauchy filter converges.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The literal class quantifies all nontrivial Cauchy filters; Cauchy means NeBot plus f×f≤uniformity. IsComplete univ is a proved equivalent formulation. Completeness supplies shrinking-trap intersections; CompleteCopy and the closed product diagonal provide the compatible complete metric for Gδ sets. It is not completeness of an arbitrary originally supplied metric.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Cauchy

A nontrivial filter whose pairs become arbitrarily uniformly close.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literal conjunction NeBot f ∧ f×ˢf≤𝓤. NeBot is a separate class asserting f≠⊥; Mathlib filters themselves allow the improper bottom filter. cauchy_iff proves the small-set entourage description, and Metric.cauchy_iff proves its epsilon-distance form. The nontriviality guard is essential to avoid false empty-space limits. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsComplete

Every Cauchy filter supported on a set has a limit in that same set.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literally ∀f,Cauchy f→f≤𝓟s→∃x∈s,f≤𝓝x. Principal-filter support means s∈f. The limit belongs to s; mere ambient convergence is insufficient. CompleteSpace is equivalent to IsComplete univ by a proved theorem. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## CauchySeq

A map whose image of the atTop filter is Cauchy; for natural-number sequences this is the usual epsilon-tail condition.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The definition supports arbitrary preorders, but the semantic bridge specializes to ℕ: ∀ε>0,∃N,∀m≥N,∀n≥N,dist(a m)(a n)<ε. This is a proved characterization, not the literal defining expression; the latter is Cauchy (Filter.map a atTop). The imported Cantor-intersection theorem uses this completeness infrastructure. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Filter.Tendsto

The mapped source filter is below the target filter.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literally Filter.map f l₁≤l₂. AtTop on natural numbers and nhds0 in the reals give convergence of the whole shrinking-diameter sequence, not just a subsequence.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.ball

Points whose distance to the center is strictly less than the radius.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The complete-metric winning strategy is centered at the actual marked point and uses a positive radius at most (1/2)^history.length. The reply contains that point and is contained in the current legal region.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.closedBall

Points at distance at most the radius from the center.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Closed bounded traps lie inside actual current inputs; the next trap lies inside the preceding open reply. No compactness or properness of closed balls is assumed.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Bornology.IsBounded

Boundedness in the compatible metric bornology; equivalently all pairwise distances on the set are bounded by some real constant.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literally IsCobounded of the complement. Bornology stores a cobounded filter, and PseudoMetricSpace.cobounded_sets constrains that filter to the distance bornology. Metric.isBounded_iff is the proved pairwise-distance bound; it is not the literal general bornology definition. Boundedness alone implies neither closedness nor compactness. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.diam

The extended nonnegative diameter converted to a real number.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Metric.diam is ENNReal.toReal of ediam; toReal∞=0, so a real diameter bound alone cannot encode boundedness. Closed traps are separately proved bounded; the finite-intersection theorem explicitly receives that hypothesis.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.ediam

The extended nonnegative diameter is the supremum of edist x y over all x and y in the set.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The supremum ranges over both point-membership proofs and may be infinity. PseudoMetricSpace.edist_dist identifies edist with ENNReal.ofReal of dist. This distinguishes the extended supremum from Metric.diam, which converts to ℝ and sends infinity to zero. Used in the complete-metric strategy and compatible-metric construction, with no compact-ball or separability assumption beyond the exact selected binders.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## CountableInterFilter

The filter is closed under intersections of countable families of its sets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Countable means an injection into ℕ; a Set is countable when its subtype is. CountableInterFilter closes membership under countable intersections. These meanings underlie Gδ enumeration and the Lindelöf countable-cover theorem. No assertion of finite branching is made.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Countable

There exists an injection from the type into the natural numbers.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Countable means an injection into ℕ; a Set is countable when its subtype is. CountableInterFilter closes membership under countable intersections. These meanings underlie Gδ enumeration and the Lindelöf countable-cover theorem. No assertion of finite branching is made.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Set.Countable

The subtype of elements of the set is countable.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Countable means an injection into ℕ; a Set is countable when its subtype is. CountableInterFilter closes membership under countable intersections. These meanings underlie Gδ enumeration and the Lindelöf countable-cover theorem. No assertion of finite branching is made.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsClosed

The complement is open.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The product diagonal is closed by coordinate equality in a metric ambient space. Closed-embedding transfer, not mere arbitrary subspace transfer, is used to obtain completeness.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsGδ

A countable intersection of ambient open sets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The literal countable set-family intersection is equivalent by a proved theorem to an ℕ-indexed intersection of opens, including an empty family represented by all universes. Image Gδ is formed by countably many node implications V_lᶜ∪⋃n V_child; the complement clause is closed, hence Gδ in a metric ambient space.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## PseudoMetrizableSpace

A countably generated uniformity induces exactly the given topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. This literal existential uniformity definition is not itself a chosen pseudometric. The pinned compatible-uniformity and metrizableSpaceMetric constructions prove/preserve the topology equality; adding T0 gives a genuine metric.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## MetrizableSpace

The given topology admits a metric.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literally extends PseudoMetrizableSpace and T0Space. The exact equality of the chosen metric topology with the supplied topology is checked in both entrypoints; arbitrary unrelated topologies are not allowed.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsCompletelyMetrizableSpace

There exists a complete metric inducing exactly the given topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The complete field supplies a MetricSpace together with topology equality and CompleteSpace for its uniformity. A replacement compatible metric may differ from a previously given incomplete one. The Gδ proof constructs a closed diagonal in a countable product of complete copies and transfers this property by homeomorphism.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## PolishSpace

Second countable and completely metrizable for the given topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The literal class extends both classes. In the main iff, second countability and metrizability are explicit ambient assumptions. Complete metric spaces need not be separable; the general forward game theorem makes no Polish conclusion without second countability.

Used by: OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## SecondCountableTopology

The topology is generated by a countable family of subsets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The literal field gives a countable generating family, not directly the directed basis axioms. Finite intersections give an actual basis; the retained proved basis bridges justify countable-basis prose. This yields hereditary Lindelöfness for the countable response covers and is required by the proved converse.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsTopologicalBasis

A downward locally directed covering family generating the topology.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The three fields are common-refinement at a point, covering the universe, and topology equality with generateFrom. Countable subbasis and countable basis are related by proved finite-intersection constructions, not identical literal declarations.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Topology.IsInducing

The domain topology equals the topology induced by the map.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Open source sets are preimages of ambient opens. Equality here is essential to lift actual strategy replies to ambient node regions.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Topology.IsEmbedding

An inducing map that is injective.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Injectivity and exact induced topology, not merely continuity, make the range homeomorphic to the source. The image Gδ theorem requires a second-countable metric codomain, with no ambient completeness premise.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## TopologicalSpace.induced

The open subsets are precisely preimages of ambient open sets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Subtype topologies and homeomorphic range transfers use this meaning; the source topology is preserved rather than silently replaced by a different topology.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Homeomorph

A bijection with continuous forward and inverse maps.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The closed product diagonal is homeomorphic to the Gδ subtype; a source embedding is homeomorphic to its range. Complete metrizability transfers through these homeomorphisms as a topology property, whereas completeness of a particular metric need not.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## TopologicalSpace.Opens

An ambient open subset bundled with its openness proof.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The countable-intersection support result accepts any ℕ-family of such opens, with no nonempty, separable or second-countable premise. Empty opens and empty total intersection are allowed.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## TopologicalSpace.Opens.CompleteCopy

The open-set subtype equipped with a special complete compatible metric.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The type synonym alone does not provide completeness. Its distance is ambient distance plus the absolute difference of reciprocals of distance to the complement. Its topology is definitionally the original subtype topology; the pinned metric/completeness instances prove those claims. Completeness needs the ambient metric complete, without second countability. If complement is empty the infDist convention is zero; no positivity is assumed there.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsLindelof

Every open cover has a countable subcover.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. This is a proved equivalence: the literal definition quantifies nontrivial CountableInterFilter filters containing the set and a cluster point inside it. The indexed ℕ-cover theorem additionally needs a nonempty index type; Node.hit supplies the required nonempty marked choices in the converse. No compactness or finite subcover is claimed.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsHereditarilyLindelof

Every subset is Lindelöf.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The literal quantification is over all subsets, including non-open ones. The second-countability instance supplies this property for the ambient metric space, hence all parent trace subsets admit countable response covers.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## HereditarilyLindelofSpace

The entire space is hereditarily Lindelöf.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The field plus the subset quantifier gives IsLindelof for each parent subset; the countable-cover selection uses a proved theorem, never a finite-subcover assertion.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## UniformSpace.Completion

The Hausdorff completion of a uniform space.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Literally SeparationQuotient(CauchyFilter X). CauchyFilter is the type of Cauchy filters; SeparationQuotient identifies inseparable points. The canonical map is uniformly inducing, and injective for T0 spaces. Its completion is complete and carries the compatible metric extension. Our source is metrizable, so the chosen metric is T0; its completion is second countable via the existing exact instances. No desired strong-game equivalence is imported.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## CauchyFilter

A filter together with proof it is Cauchy.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Cauchy includes nontriviality; completion does not identify arbitrary filters as points. The Hausdorff quotient then identifies topologically inseparable Cauchy-filter representatives.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## SeparationQuotient

The quotient by the inseparable-point relation.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Inseparable means equality of neighborhood filters. The separated completion has a T0 topology; a source already T0 embeds injectively.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Inseparable

Two points have equal neighborhood filters.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. T0Space forces such points equal. This accounts for the separation condition in metrization and injectivity of the canonical completion map.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## T0Space

Inseparable points are equal.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The MetrizableSpace class includes T0, turning a compatible pseudometric into a metric and making completion coercion injective.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Set.range

The points equal to some image value.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The image Gδ conclusion is exactly the existential range, not its closure or a larger completion. The shrinking-diameter argument proves every point of the node-implication Gδ equals f x for one winning point x.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.infDist

The real value of the extended infimum distance to a subset.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. InfDist is ENNReal.toReal of infEDist; it is zero for the empty subset. CompleteCopy uses the complement of an open set, with the boundary argument distinguishing whether an excluded limit exists. No arbitrary strictly positive distance to an empty complement is assumed.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Metric.infEDist

The infimum of extended distances to the subset.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. An infimum over the empty set is infinity; conversion to real infDist then yields zero. CompleteCopy boundary terms use precisely this convention.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## ClusterPt

The neighborhood filter and supplied filter have nontrivial infimum.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. This is the exact cluster-point relation in the literal IsLindelof definition; convergence is not required by that definition. Countable subcover is a proved equivalence.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## SeparableSpace

A countable dense subset exists.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Second countability supplies separability, which passes to the completion through the canonical dense map. A separable metric completion is second countable. This instance chain does not assert that every complete metric space is separable.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Filter.IsCountablyGenerated

The filter is generated by some countable set of sets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The out field gives f=Filter.generate s for countable s. GenerateSets is the finite-intersection, superset and universe closure of generators. This countability, plus uniform-space axioms and T0 separation, gives the compatible metric used in MetrizableSpace; it is distinct from CountableInterFilter.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Filter.generate

The filter generated by the supplied sets.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. Its membership predicate GenerateSets is inductively closed under generator membership, universe, supersets and binary intersection. In the reverse-inclusion order this is the largest filter containing the generators. It is not countable-intersection closure.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Topology.IsClosedEmbedding

An embedding with closed range.

Inherited through the byte-identical StrongChoquetFoundation proof of the Polish criterion, then the image results. The closed product diagonal and homeomorphisms provide closed embeddings for complete-metrizability transfer. The original completion image is not asserted closed; it is Gδ. The embedding into its own range is a homeomorphism.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Disjoint

Any common lower bound lies below bottom.

For filters this is disjoint neighborhood filters; the compiled separated-neighborhood equivalence interprets it as disjoint open neighborhoods.

Used by: OpenPolish.polish_image_of_t3


## nhdsSet

Supremum of neighborhood filters of points of the set.

Point neighborhoods are the retained nhds infimum of open principal filters. The compiled RegularSpace equivalence connects filter disjointness with disjoint open sets.

Used by: OpenPolish.polish_image_of_t3


## SeparatedNhds

Two sets lie inside disjoint open sets.

The retained separatedNhds_iff_disjoint and separately compiled regularity equivalence connect this literal existential definition with the filter class field.

Used by: OpenPolish.polish_image_of_t3


## Continuous

Preimages of open target sets are open.

Continuity forms the open lifted source regions.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## IsOpenMap

Images of every open source set are open.

Makes projected replies open; does not assert continuity or surjectivity.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Topology.IsOpenQuotientMap

Surjective, continuous and open.

Its inherited countable basis theorem supplies target second countability.

Used by: OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## RegularSpace

A point outside a closed set has disjoint neighborhoods from it.

Canonical filter-field definition; with T0 gives T3, then second countability invokes Urysohn metrizability. Both entrypoints prove equivalence with disjoint open neighborhoods of every closed set and excluded point.

Used by: OpenPolish.polish_image_of_t3


## T3Space

T0 plus regularity, which implies Hausdorff separation.

No inference of regularity merely from Hausdorffness.

Used by: OpenPolish.polish_image_of_t3


## Set.image

Existential forward image.

Membership retains one actual witness; image of an infinite intersection is not equated with intersection of images.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Set.preimage

Inverse-image membership means the function value belongs to the target set.

Source regions are inverse images intersected with the previous lifted response whenever a constrained lift exists.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Set.inter

Conjunction of membership in two sets.

Ensures the next lifted region lies in the previous source response.

Used by: OpenPolish.imageStrategy_winning, OpenPolish.strong_image, OpenPolish.completelyMetrizable_image, OpenPolish.polish_image, OpenPolish.polish_image_of_t3


## Source Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256 `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`; Git blob `326105821a5a8ce5041ccf8dce22779bd55fa923`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L145-L147

```lean
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L107-L109

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L162-L162

```lean
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L182-L188

```lean
structure IsOpenQuotientMap (f : X → Y) : Prop where
  /-- An open quotient map is surjective. -/
  surjective : Function.Surjective f
  /-- An open quotient map is continuous. -/
  continuous : Continuous f
  /-- An open quotient map is an open map. -/
  isOpenMap : IsOpenMap f
```


## Source Mathlib/Topology/Closure.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean

SHA256 `d4e49fd0b092d34d5db79261bfc58b69ad3383a113ff2a0f54c0912a8b9afb5c`; Git blob `557a4cd1768bc437e6f55fd9635ad07eba7c6080`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean#L407-L416

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


## Source Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256 `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`; Git blob `866ef6ab673f737a4ffbb7b2138402d5c76e6c05`. Apache-2.0.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L266-L266

```lean
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L242-L242

```lean
protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}
```


## Source Mathlib/Topology/MetricSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

SHA256 `cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9`; Git blob `10910c95e518dfacb8d4fcb88d7e689315791952`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L54-L71

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


## Source Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

SHA256 `13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35`; Git blob `912bc464320d8ea70f002255c59e9f79d41f6ac2`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L100-L108

```lean

/-- The distance function (given an ambient metric space on `α`), which returns
a real number `dist x y` given `x y : α`. This type class does not enforce non-negativity. -/
@[ext]
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ

export Dist (dist)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L124-L153

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L368-L375

```lean
/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
@[wikidata Q838611]
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L420-L426

```lean
/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L625-L629

```lean
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L833-L841

```lean
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball

```


## Source Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

SHA256 `7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f`; Git blob `c2269f217cc1266e8d378b9493c90e1480a0c438`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L164-L166

```lean
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff
```


## Source Mathlib/Topology/MetricSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

SHA256 `9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618`; Git blob `4f65c04a3aac9896699e53b84846de79031d9836`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean#L53-L61

```lean
section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff
```


## Source Mathlib/Topology/UniformSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256 `0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c`; Git blob `3f068a41cafe8605be201dd24b3843bcbba45a6e`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L185-L209

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L700-L714

```lean
/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `IsUniformEmbedding`. -/
@[mk_iff, fun_prop]
structure IsUniformInducing (f : α → β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α ↦ (f x.1, f x.2)) (𝓤 β) = 𝓤 α

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff, fun_prop]
structure IsUniformEmbedding (f : α → β) : Prop extends IsUniformInducing f where
  /-- A uniform embedding is injective. -/
  injective : Function.Injective f
```


## Source Mathlib/Topology/UniformSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

SHA256 `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`; Git blob `86640c96b74c3a4161ecae8151f0cdec46f6d64c`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33

```lean

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L35-L38

```lean
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L47-L53

```lean
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L184-L188

```lean
/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373

```lean
/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L407-L412

```lean
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L920-L930

```lean

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. -/
instance secondCountable_of_separable [SeparableSpace α] : SecondCountableTopology α := by
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩
  obtain
    ⟨t : ℕ → SetRel α α, hto : ∀ i : ℕ, t i ∈ (𝓤 α).sets ∧ IsOpen (t i) ∧ (t i).IsSymm,
      h_basis : (𝓤 α).HasAntitoneBasis t⟩ :=
    (@uniformity_hasBasis_open_symmetric α _).exists_antitone_subbasis
  choose ht_mem hto hts using hto
```


## Source Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256 `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`; Git blob `343fd3e5f576a8e0f0f040eb2df8e5c309106655`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L221-L222

```lean
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L235-L245

```lean

instance : IsEquiv X Inseparable :=
  inferInstanceAs <| IsEquiv X (Eq.onFun 𝓝)

/-- A `setoid` version of `Inseparable`, used to define the `SeparationQuotient`. -/
@[instance_reducible]
def inseparableSetoid : Setoid X := { Setoid.comap 𝓝 ⊥ with r := Inseparable }

/-- The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov
quotient. This quotient is guaranteed to be a T₀ space. -/
def SeparationQuotient := Quotient (inseparableSetoid X)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L275-L276

```lean
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L161-L162

```lean
def nhdsSet (s : Set X) : Filter X :=
  sSup (nhds '' s)
```


## Source Mathlib/Topology/Neighborhoods.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

SHA256 `ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a`; Git blob `8bfc6cc6c85396ab77a34b0725508d165b3903f4`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
```


## Source Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256 `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`; Git blob `760285d16af8795fa73313254a28aa651c9d0883`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L183-L190

```lean
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L444-L452

```lean
/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters. -/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L158

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L268-L277

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L405-L423

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L425-L439

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


## Source Mathlib/Order/Filter/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

SHA256 `5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb`; Git blob `13734fc09a2dff6db46ca52140aceb45d45eccd8`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L365-L367

```lean
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L163-L174

```lean
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter
```


## Source Mathlib/Order/Filter/Prod.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

SHA256 `2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367`; Git blob `9ba0b26e290fe850ba43a785d59881ff873a8936`. Apache-2.0.

```lean
/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean#L52-L59

```lean
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

```


## Source Mathlib/Basic/ENNReal/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean

SHA256 `211629947deb3d78a8541202d33a9fed3d4c8f22215daea3d7d37209a824d947`; Git blob `75cadd3fae3f45e1e88abe228266fa115ef5552b`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean#L280-L284

```lean
  ext; simp [coe_toNNReal_eq_toReal]

@[simp] theorem toNNReal_top : ∞.toNNReal = 0 := rfl

@[simp] theorem toReal_top : ∞.toReal = 0 := rfl
```


## Source Mathlib/Order/Filter/Tendsto.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

SHA256 `76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce`; Git blob `7f85e578caf6eb1d37a45af5203cd059335be9b8`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean#L31-L33

```lean
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
```


## Source Mathlib/Order/Filter/AtTopBot/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

SHA256 `4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621`; Git blob `6cf35ed92a409e5acf84c90305ecc7d1dd638619`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L29-L40

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


## Source Mathlib/Topology/Bornology/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

SHA256 `427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e`; Git blob `4b142e1d604446eafb9ee39b6a39a492d687c997`. Apache-2.0.

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L48-L55

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L90-L101

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


## Source Mathlib/Topology/MetricSpace/Bounded.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

SHA256 `dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b`; Git blob `b47b2b389eebc08df32ef3a6f450f350c389cfcd`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L405-L411

```lean
/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the `ediam` -/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (ediam s)

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L564-L570

```lean
/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

```


## Source Mathlib/Topology/EMetricSpace/Diam.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean

SHA256 `699ba791a149bdcdc24e9d7d650aa34925e04947d38df7e7c1ef9c9bd195822f`; Git blob `d5a39e2f435e837f92a9ed3c804f61d9f6240bbf`. Apache-2.0.

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean#L24-L34

```lean

namespace Metric

section WeakPseudoEMetricSpace

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam [EDist X] (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]

```


## Source Mathlib/Topology/GDelta/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean

SHA256 `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`; Git blob `feae671419368d0d284d9ed57c536b6b54afba33`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L173-L174

```lean
instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L63-L64

```lean
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L91-L103

```lean
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

/-- The intersection of an encodable family of Gδ sets is a Gδ set. -/
```


## Source Mathlib/Order/Filter/CountableInter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean

SHA256 `b6854464b88925956362116ea97e5e427b6955f99ab714d32900a15e00c230fd`; Git blob `e23749c7d2e55ce5ed83a21b279237a700d20a54`. Apache-2.0.

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L42-L44

```lean
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L272-L277

```lean
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L281-L283

```lean
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ ↦ .sInter) fun _ _ ↦ .superset
deriving CountableInterFilter
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L289-L305

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean#L166-L173

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


## Source Mathlib/Basic/Countable/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

SHA256 `d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f`; Git blob `2718dae9396dc0acff5f8b703d3587512b0281db`. Apache-2.0.

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41-L46

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'
```


## Source Mathlib/Data/Set/Countable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

SHA256 `047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98`; Git blob `f5ffd2035308f61e38f10aad4df99b2405ec519a`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L40-L49

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


## Source Mathlib/Topology/Metrizable/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean

SHA256 `b3109255e290e85cfeaca128a66def49978c4e9fe22866c499e9882132bd3ac8`; Git blob `a018e7cd9cf73cca86af3af0ae8a63aa6f463f20`. Apache-2.0.

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L42-L44

```lean
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L125-L126

```lean
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L54-L63

```lean
-- see note [reducible non-instances]
noncomputable abbrev pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : UniformSpace X :=
  h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm

example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

```


## Source Mathlib/Topology/Metrizable/Uniformity.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Uniformity.lean

SHA256 `57cd395dfc2492244906b4cd136ca48bf553fca053e5fdb3033132f105a7d265`; Git blob `79e68cd4e8e930ab7b13e9b4e96e35b8a0101d55`. Apache-2.0.

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Uniformity.lean#L265-L284

```lean
noncomputable abbrev TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X : Type*)
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformSpace = t.pseudoMetrizableSpaceUniformity := by
  with_reducible_and_instances rfl

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable abbrev TopologicalSpace.metrizableSpaceMetric (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : MetricSpace X :=
  letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl

```


## Source Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

SHA256 `45e2fe2d79f14e9cf4e87f13f413eef94b418384fc3eaad3dce7b1a730ed54c9`; Git blob `a09f9b3b228345d4c4648901cbaa79885a10349f`. Apache-2.0.

```lean
/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L154-L156

```lean
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L191-L211

```lean
noncomputable def completelyMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] : MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert! h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeIsCompletelyMetrizable X`. -/
@[instance_reducible]
noncomputable
def upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    UpgradedIsCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace IsCompletelyMetrizableSpace

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L247-L258

```lean
/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L219-L225

```lean
/-- A countable product of completely metrizable spaces is completely metrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (Π i, X i) := by
  let := fun i ↦ upgradeIsCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L293-L297

```lean
/-- A closed subset of a completely metrizable space is also completely metrizable. -/
theorem _root_.IsClosed.isCompletelyMetrizableSpace
    [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace
```


## Source Mathlib/Topology/MetricSpace/Polish.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean

SHA256 `71c9682ea53f194d1587fbd41695e35cc7fb8f51b1503f695ba4adfb15c52059`; Git blob `ec205e848d4f8eabd112e1eb2c68327c0fac206a`. Apache-2.0.

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L62-L63

```lean
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L157-L157

```lean
def CompleteCopy {α : Type*} [MetricSpace α] (s : Opens α) : Type _ := s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L164-L177

```lean
instance instDist : Dist (CompleteCopy s) where
  dist x y := dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)

theorem dist_eq (x y : CompleteCopy s) :
    dist x y = dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ) :=
  rfl

theorem dist_val_le_dist (x y : CompleteCopy s) : dist x.1 y.1 ≤ dist x y :=
  le_add_of_nonneg_right (abs_nonneg _)

instance : TopologicalSpace (CompleteCopy s) := inferInstanceAs (TopologicalSpace s)
instance [SecondCountableTopology α] : SecondCountableTopology (CompleteCopy s) :=
  inferInstanceAs (SecondCountableTopology s)
instance : T0Space (CompleteCopy s) := inferInstanceAs (T0Space s)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L188-L212

```lean
instance instMetricSpace : MetricSpace (CompleteCopy s) := by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ ↦ ?_) (fun _ _ ↦ ?_) (fun x y z ↦ ?_) fun t ↦ ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z = dist x.1 z.1 + |1 / infDist x.1 sᶜ - 1 / infDist z.1 sᶜ| := rfl
      _ ≤ dist x.1 y.1 + dist y.1 z.1 + (|1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ| +
            |1 / infDist y.1 sᶜ - 1 / infDist z.1 sᶜ|) :=
        add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
      _ = dist x y + dist y z := add_add_add_comm ..
  · refine ⟨fun h x hx ↦ ?_, fun h ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩
    · rcases (Metric.isOpen_iff (α := s)).1 h x hx with ⟨ε, ε0, hε⟩
      exact ⟨ε, ε0, fun y hy ↦ hε <| (dist_comm _ _).trans_lt <| (dist_val_le_dist _ _).trans_lt hy⟩
    · rcases h x hx with ⟨ε, ε0, hε⟩
      simp only [dist_eq, one_div] at hε
      have : Tendsto (fun y : s ↦ dist x.1 y.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist y.1 sᶜ)⁻¹|)
          (𝓝 x) (𝓝 (dist x.1 x.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist x.1 sᶜ)⁻¹|)) := by
        refine (tendsto_const_nhds.dist continuous_subtype_val.continuousAt).add
          (tendsto_const_nhds.sub <| ?_).abs
        refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
        rw [s.isOpen.isClosed_compl.closure_eq, mem_compl_iff, not_not]
        exact x.2
      simp only [dist_self, sub_self, abs_zero, zero_add] at this
      exact mem_of_superset (this <| gt_mem_nhds ε0) hε
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L214-L240

```lean
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (CompleteCopy s) := by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu ↦ ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m hNn hNm).le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by norm_num)
  obtain ⟨x, xlim⟩ : ∃ x, Tendsto (fun n => (u n).1) atTop (𝓝 x) := cauchySeq_tendsto_of_complete A
  by_cases xs : x ∈ s
  · exact ⟨⟨x, xs⟩, tendsto_subtype_rng.2 xlim⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, 1 / infDist (u n).1 sᶜ < C := by
    refine ⟨(1 / 2) ^ 0 + 1 / infDist (u 0).1 sᶜ, fun n ↦ ?_⟩
    rw [← sub_lt_iff_lt_add]
    calc
      _ ≤ |1 / infDist (u n).1 sᶜ - 1 / infDist (u 0).1 sᶜ| := le_abs_self _
      _ = |1 / infDist (u 0).1 sᶜ - 1 / infDist (u n).1 sᶜ| := abs_sub_comm _ _
      _ ≤ dist (u 0) (u n) := le_add_of_nonneg_left dist_nonneg
      _ < (1 / 2) ^ 0 := hu 0 0 n le_rfl n.zero_le
  have Cpos : 0 < C := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hC 0)
  have Hmem : ∀ {y}, y ∈ s ↔ 0 < infDist y sᶜ := fun {y} ↦ by
    rw [← s.isOpen.isClosed_compl.notMem_iff_infDist_pos ⟨x, xs⟩]; exact not_not.symm
  have I : ∀ n, 1 / C ≤ infDist (u n).1 sᶜ := fun n ↦ by
    have : 0 < infDist (u n).1 sᶜ := Hmem.1 (u n).2
    rw [div_le_iff₀' Cpos]
    exact (div_le_iff₀ this).1 (hC n).le
  have I' : 1 / C ≤ infDist x sᶜ :=
    have : Tendsto (fun n => infDist (u n).1 sᶜ) atTop (𝓝 (infDist x sᶜ)) :=
      ((continuous_infDist_pt (sᶜ : Set α)).tendsto x).comp xlim
```


## Source Mathlib/Topology/Sets/Opens.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Opens.lean

SHA256 `d41320cc09de94b691658557d424c02f2e1a23999aa9d327fce25ee74adb2185`; Git blob `8d4237b2ac3ae77ef45ee7edd5e2df82b9cb1abd`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Opens.lean#L65-L69

```lean
structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier
```


## Source Mathlib/Topology/Defs/Induced.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

SHA256 `ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74`; Git blob `7526293e644df38a5a2564f8c52a2bd7f561fc82`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L64-L67

```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L132-L134

```lean
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L147-L149

```lean
structure IsEmbedding (f : X → Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L159-L161

```lean
structure IsClosedEmbedding (f : X → Y) : Prop extends IsEmbedding f where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f
```


## Source Mathlib/Topology/Homeomorph/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean

SHA256 `4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72`; Git blob `7c7e9c3c815eb873ab5e637aaac83e4cdf80f39d`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L43-L51

```lean
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L297-L300

```lean
theorem isClosedEmbedding (h : X ≃ₜ Y) : IsClosedEmbedding h :=
  .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap

theorem preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
```


## Source Mathlib/Topology/Bases.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean

SHA256 `fbd29cb53487d8ff54efda38cd831d4966a19a052654ef39a09352753986d1d6`; Git blob `4165527ffdf10c235881bc6738e99ad2bf6b1b07`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L793-L795

```lean
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L73-L79

```lean
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards. -/
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  /-- The sets from `s` cover the whole space. -/
  sUnion_eq : ⋃₀ s = univ
  /-- The topology is generated by sets from `s`. -/
  eq_generateFrom : t = generateFrom s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L797-L804

```lean
protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩

lemma SecondCountableTopology.mk' {α} {b : Set (Set α)} (hc : b.Countable) :
    @SecondCountableTopology α (generateFrom b) :=
  @SecondCountableTopology.mk α (generateFrom b) ⟨b, hc, rfl⟩

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L346-L348

```lean
@[mk_iff] class SeparableSpace : Prop where
  /-- There exists a countable dense set. -/
  exists_countable_dense : ∃ s : Set α, s.Countable ∧ Dense s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L811-L815

```lean
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, notMem_sdiff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).sdiff_empty⟩
  exacts [((countable_ofPred_finite_subset hb₁).image _).mono sdiff_subset, rfl]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L915-L920

```lean
instance (priority := 100) SecondCountableTopology.to_separableSpace [SecondCountableTopology α] :
    SeparableSpace α := by
  choose p hp using fun s : countableBasis α => nonempty_of_mem_countableBasis s.2
  exact ⟨⟨range p, countable_range _, (isBasis_countableBasis α).dense_iff.2 fun o ho _ =>
          ⟨p ⟨o, ho⟩, hp ⟨o, _⟩, mem_range_self _⟩⟩⟩

```


## Source Mathlib/Topology/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256 `2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5`; Git blob `b8acdd3aee23b43330bc36aa8f7f1819a16a2a55`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L62-L75

```lean
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set α), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)

/-- The smallest topological space containing the collection `g` of basic sets -/
@[instance_reducible]
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

```


## Source Mathlib/Topology/Compactness/Lindelof.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean

SHA256 `e75a097a0ac483a700c8eb13d91246dd151d3e34edf331f8fcb4f4f15fbe505d`; Git blob `cf1dc92979e8bceb698d5d862049056ec9b51779`. Apache-2.0.

```lean
/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L51-L52

```lean
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L292-L296

```lean
theorem isLindelof_iff_countable_subcover :
    IsLindelof s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ↦ hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L184-L196

```lean
theorem IsLindelof.indexed_countable_subcover {ι : Type v} [Nonempty ι]
    (hs : IsLindelof s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ f : ℕ → ι, s ⊆ ⋃ n, U (f n) := by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (Set.countable_iff_exists_surjective c_nonempty).mp c_count
  refine ⟨fun x ↦ f x, c_cov.trans <| iUnion₂_subset_iff.mpr (?_ : ∀ i ∈ c, U i ⊆ ⋃ n, U (f n))⟩
  intro x hx
  obtain ⟨n, hn⟩ := f_surj ⟨x, hx⟩
  exact subset_iUnion_of_subset n <| subset_of_eq (by rw [hn])

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L696-L697

```lean
def IsHereditarilyLindelof (s : Set X) :=
  ∀ t ⊆ s, IsLindelof t
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L700-L702

```lean
class HereditarilyLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Hereditarily Lindelöf space, `Set.univ` is a Hereditarily Lindelöf set. -/
  isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L714-L734

```lean
theorem HereditarilyLindelofSpace.isLindelof [HereditarilyLindelofSpace X] (s : Set X) :
    IsLindelof s := by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

theorem HereditarilyLindelofSpace.of_forall_isOpen (H : ∀ s : Set X, IsOpen s → IsLindelof s) :
    HereditarilyLindelofSpace X := by
  refine ⟨fun s _ ↦ isLindelof_of_countable_subcover fun U U_open hU ↦ ?_⟩
  obtain ⟨t, t_count, ht⟩ := H (⋃ i, U i) (isOpen_iUnion U_open)
    |>.elim_countable_subcover U U_open subset_rfl
  exact ⟨t, t_count, hU.trans ht⟩

instance (priority := 100) SecondCountableTopology.toHereditarilyLindelof
    [SecondCountableTopology X] : HereditarilyLindelofSpace X where
  isHereditarilyLindelof_univ t _ _ := by
    apply isLindelof_iff_countable_subcover.mpr
    intro ι U hι hcover
    have := @isOpen_iUnion_countable X _ _ ι U hι
    rcases this with ⟨t, ⟨htc, htu⟩⟩
    use t, htc
    exact subset_of_subset_of_eq hcover (id htu.symm)
```


## Source Mathlib/Topology/UniformSpace/Completion.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean

SHA256 `f4b1dfd61e36cdf4edab03a17a87eff5c26d2ed42988e8981fb49a0e3056dbbc`; Git blob `e7e1caa48b7abeb673eed6a7d7f69cbbbf4cea8e`. Apache-2.0.

```lean
/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean#L60-L61

```lean
def CauchyFilter (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean#L291-L291

```lean
def Completion := SeparationQuotient (CauchyFilter α)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean#L298-L309

```lean
instance uniformSpace : UniformSpace (Completion α) :=
  fast_instance% SeparationQuotient.instUniformSpace

instance completeSpace : CompleteSpace (Completion α) :=
  SeparationQuotient.instCompleteSpace

instance t0Space : T0Space (Completion α) := SeparationQuotient.instT0Space

variable {α} in
/-- The map from a uniform space to its completion. -/
@[coe] def coe' : α → Completion α := SeparationQuotient.mk ∘ pureCauchy

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean#L355-L357

```lean
theorem isUniformEmbedding_coe [T0Space α] : IsUniformEmbedding ((↑) : α → Completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α
    injective := separated_pureCauchy_injective }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Completion.lean#L377-L378

```lean
instance separableSpace_completion [SeparableSpace α] : SeparableSpace (Completion α) :=
  Completion.isDenseInducing_coe.separableSpace
```


## Source Mathlib/Topology/MetricSpace/Completion.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Completion.lean

SHA256 `d407528c23967cf9caf98c4eb9765cc3f4a9cbe1557295da5d6ebd40c49d86d7`; Git blob `0dc0da1313789224d70f1c232e110ed926c0f9d9`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Completion.lean#L149-L156

```lean
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _
```


## Source Mathlib/Topology/Separation/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean

SHA256 `96c74f410b14c3adecc1cb06d90d9d7a61bbb1529c18000426687bee99ba6991`; Git blob `2d39660bfd78f367e80c7ee07b36871de306e3f2`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L77-L79

```lean
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y
```


## Source Mathlib/Topology/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean

SHA256 `47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f`; Git blob `91a7136cc7b39e609f8becbf9e0785069bb2610d`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L66-L68

```lean
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)
```


## Source Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256 `60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e`; Git blob `f5d18fca655f6bf3079f859060f3738b5f2bc089`. Apache-2.0.

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L173-L173

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L135-L135

```lean
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}
```


## Source Mathlib/Topology/MetricSpace/HausdorffDistance.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/HausdorffDistance.lean

SHA256 `9bdca849e0d34aee7a027af90d5d0fc5ba04b9a0742ed2c882ed577904fe41f9`; Git blob `89edc72a5118131c9c67c870bc66510d8f158e9a`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/HausdorffDistance.lean#L463-L464

```lean
def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEDist x s)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/HausdorffDistance.lean#L76-L77

```lean
def infEDist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y
```


## Source Mathlib/Order/Filter/CountablyGenerated.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountablyGenerated.lean

SHA256 `5628113472da223e2345cc12426ec269ca87c2e233eb76e9789ed1c21719f2d0`; Git blob `1732fded7e6e4de54b0ee7290f109aa998c7d880`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountablyGenerated.lean#L29-L32

```lean
/-- `IsCountablyGenerated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  /-- There exists a countable set that generates the filter. -/
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s
```


## Source Mathlib/Topology/Homeomorph/Lemmas.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Lemmas.lean

SHA256 `e76ff3b356c5cff8dafa5ebdb561b7f439ad7d687e0def918e6512e36ef02e9e`; Git blob `6baab7e4c182041ffe730e81632aaec349057894`. Apache-2.0.

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Lemmas.lean#L408-L415

```lean
namespace Topology.IsEmbedding

/-- Homeomorphism given an embedding. -/
@[simps! apply_coe]
noncomputable def toHomeomorph {f : X → Y} (hf : IsEmbedding f) :
    X ≃ₜ Set.range f :=
  Equiv.ofInjective f hf.injective |>.toHomeomorphOfIsInducing <|
    IsInducing.subtypeVal.of_comp_iff.mp hf.toIsInducing
```


## Source Mathlib/Topology/UniformSpace/UniformEmbedding.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/UniformEmbedding.lean

SHA256 `d654b7daf50aa5ec57538e3e957509ceb738bc764213858cd4a5aa98d60355f8`; Git blob `1aaf86a3677273ffa84beb6c50b384428c8da5f6`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/UniformEmbedding.lean#L214-L218

```lean
protected lemma IsUniformEmbedding.isEmbedding {f : α → β} (h : IsUniformEmbedding f) :
    IsEmbedding f where
  toIsInducing := h.toIsUniformInducing.isInducing
  injective := h.injective

```


## Source Mathlib/Order/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

SHA256 `5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c`; Git blob `7d5339050bb81a9d325ca7536bbe37dba409813f`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L48-L49

```lean
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```


## Source Mathlib/Topology/Separation/SeparatedNhds.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/SeparatedNhds.lean

SHA256 `7dacfeb4638974042822ced1e423db45923eeb3253bd35727a64ae6abb026022`; Git blob `37b8c1e46dbcf3ae72c37ccb3a3750d47563086c`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/SeparatedNhds.lean#L46-L47

```lean
def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/SeparatedNhds.lean#L49-L52

```lean
theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

```


## Source Mathlib/Topology/Separation/Regular.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Regular.lean

SHA256 `f0f2120650baa283c15069a4403d2a1eadeef74204bff44fa3f4b5543eaa94f0`; Git blob `ab8ac2866c917f921ebfd21ae7c876899707775a`. Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Regular.lean#L79-L82

```lean
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods. -/
  regular : ∀ {s : Set X} {a}, IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Regular.lean#L441-L441

```lean
class T3Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, RegularSpace X
```
