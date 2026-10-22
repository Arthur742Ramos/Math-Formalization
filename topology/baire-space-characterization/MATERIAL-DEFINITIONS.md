# Material imported definitions

Exact immutable Mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55. Core compiler evidence is retained separately in verification/core-imported-definitions.json.

## TopologicalSpace

A topology is an open-set predicate closed under univ, finite intersections and arbitrary unions. Every open, closure, continuous and open-map assertion uses the supplied topology. In the metric versions its compatibility is recorded by the metric/uniformity fields; the Polish version uses an equal compatible complete metric, not a new topology.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## IsOpen

The open-set predicate of the ambient topology. The refinement sets and all scheme nodes are genuinely open. Exact cylinder-image equality, together with the product cylinder basis, yields openness of the limit map on arbitrary opens.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## closure

The intersection of all closed supersets of a set. Closure-child containment is proved because every child is clopen, hence equal to its closure, and is contained in its parent. The complete-space limit belongs to every node, not merely its closure.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## IsClosed

A set is closed when its complement is open. Every constructed scheme node is clopen and therefore closed. In the complete ambient metric its closedness also gives set completeness, used to contradict total boundedness of a noncompact node. No compactness of closed balls is used.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## Set.Nonempty

There exists an element belonging to the set. Every clopen node and every final partition child is nonempty. Repetitions are allowed only in the preliminary countable cover; after disjointification, empty differences are removed and the infinite survivor subtype is reindexed bijectively by naturals.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## MetricSpace

A real-valued pseudometric separating points, with stored compatible uniformity and topology. A compatible separating metric gives uniqueness of branch limits. Clopen neighborhoods refine small open balls. Completeness plus failure of compactness supplies a scale forbidding finite ball covers; no properness or compact-ball assumption is used.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## PseudoMetricSpace

Symmetric real-valued distance with reflexivity and triangle inequality, plus compatible extended distance, uniformity, topology and bornology. The fields edist_dist and uniformity_dist identify the extended diameter and filter completeness with the real metric. The actual selected metric is separating because MetricSpace extends this class.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## UniformSpace

A uniformity filter on pairs with symmetry and composition, compatible with the stored topology through neighborhood comaps. CompleteSpace is stated for this uniformity. Compatibility with the metric and topology is essential: the limit is convergence for the original topology, not for an unrelated uniformity.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## CompleteSpace

Every Cauchy filter converges to a point of the space. Completeness is an explicit hypothesis of the selected partition and scheme constructions. A closed clopen parent is complete, so noncompactness forces failure of total boundedness. Generic CantorScheme totality then gives branch limits; no convergent-subsequence replacement is made.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Cauchy

A nontrivial filter whose product with itself is below the uniformity. This is the filter definition underlying CompleteSpace. In the inherited metric uniformity it agrees with the usual eventually arbitrarily close criterion, as witnessed by retained metric bridges.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## CauchySeq

The filter image of atTop under a sequence is a Cauchy filter. The full sequence of chosen points along each branch is Cauchy; totality does not merely find a convergent subsequence.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## IsComplete

Every Cauchy filter supported by the set has a limit in that set. Every Cauchy filter supported by a set has a limit in that set. Here every clopen node is complete in the chosen complete ambient metric, by closedness. This is used before the non-total-bounded scale is chosen.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Filter.Tendsto

The image filter of the source is below the target filter. VanishingDiam concerns the entire sequence of extended diameters along each branch tending to zero, indexed by natural-number atTop and the extended-nonnegative-real neighborhood filter.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Metric.ball

The set of points at real distance strictly less than the radius from a center. Preliminary clopen neighborhoods lie inside the parent intersected with a ball of radius epsilon/2. Final refinement tolerance is min(epsilon,delta/2), where delta forbids finite ball covers. Triangle inequality bounds diameter; no ball-closure containment is asserted.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## Metric.ediam

The supremum of extended distances between every pair of points in the set. The bound ediam(V)<=ofReal(epsilon) is an extended-real bound on all pairs. It does not use real diameter, whose infinity convention would be unsuitable. Geometric bounds imply VanishingDiam.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Countable

A type admits an injective function into the naturals. The preliminary countable subcover may use repetitions. Its disjointified nonempty survivor subtype is countable AND infinite; the final Nat indexing is a bijection, so final children are distinct and disjoint.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## Set.Countable

The subtype induced by the set is countable. Applies to a chosen set of cover indices, not to the underlying Polish space. The ambient space may be uncountable.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## SecondCountableTopology

The topology is generated by a countable family of subsets. Second countability supplies a countable subcover for each clopen refinement. Once a ClopenScheme is supplied, the generic exact-cylinder-image theorem requires completeness but not a separate second-countability assumption.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.IsTopologicalBasis

A family of opens that refines every open neighborhood at each of its points. The clopen-basis hypothesis refines each open neighborhood by a clopen member. The separate product cylinder basis transfers exact cylinder images to openness of the limit map.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.IsCompletelyMetrizableSpace

There exists a metric giving exactly the supplied topology whose induced uniformity is complete. upgradeIsCompletelyMetrizable chooses such a metric while preserving the TopologicalSpace instance. An arbitrary pre-existing compatible metric need not be complete.

Used by: BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## PolishSpace

The supplied topology is second-countable and admits a compatible complete metric. The supplied topology is second-countable and admits a compatible complete metric. It can hold for an empty type, so the full equivalence explicitly requires Nonempty as well. In the unrestricted converse, Polishness is derived from a Baire homeomorphism.

Used by: BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Continuous

The preimage of every open codomain set is open in the domain. The domain has the product topology of discrete naturals. Upstream VanishingDiam.map_continuous is composed with the total-domain inclusion; continuity is not inferred from surjectivity or openness.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## IsOpenMap

The image of every open domain set is open in the codomain. Every open-set image is open. Exact clopen cylinder images prove this property. Together with continuity and the separately proved bijection it gives a homeomorphism, including inverse continuity.

Used by: BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Set.image

An element belongs to the image when it is the value of the function at some element of the domain set. The image_cylinder theorem proves literal equality with the corresponding scheme open set, both inclusions. The reverse inclusion extends the prescribed finite prefix through any prescribed target point.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Set.preimage

The set of points whose function value belongs to the target set. This occurs in the literal continuity predicate. It is distinct from image and no interchange of arbitrary intersections and images is assumed.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Set.range

The image of the universal domain set. Surjectivity follows from image_cylinder at level zero, whose domain cylinder and corresponding scheme root are both univ.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.induced

A set is open for the induced topology precisely when it is the preimage of an open set under the defining function. The product topology on Baire space is the infimum of the topologies induced by each coordinate evaluation. The source coordinates use the canonical discrete topology on naturals. The partial induced-map subtype also uses the induced topology before totality is proved.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## PiNat.cylinder

Sequences agreeing with the given sequence in every coordinate strictly below n. The product cylinder uses all coordinates less than n, including the empty prefix at zero. It is not a binary path model.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## PiNat.res

The first n coordinates recorded as a reversed finite list. res x (n+1)=x n :: res x n; the newest coordinate is prepended. The branch extension and scheme-child convention match this order exactly.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## CantorScheme.inducedMap

A partial branch map whose domain consists of branches with nonempty intersection and whose value is a chosen intersection point. The limit is this partial map made total after proving every branch intersection nonempty. Its value belongs to every clopen node on that branch; disjoint siblings ensure injectivity.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## CantorScheme.ClosureAntitone

The closure of each child set is contained in its parent set. Closedness of children turns child inclusion into closure inclusion. This lets generic completeness/vanishing-diameter machinery give membership in every node along a branch.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## CantorScheme.VanishingDiam

On every infinite branch, extended diameters of its finite-prefix sets tend to zero. The constructed bound is ofReal((1/2)^length) at every positive depth. The root need not be bounded. Completeness and nonempty nodes imply totality; vanishing diameter also implies continuity.

Used by: BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## ENNReal.ofReal

A real converted to the extended nonnegative reals by truncating negative values to zero. All requested refinement radii epsilon are strictly positive; all geometric diameter bounds are positive. No infinity-to-zero real-diameter conversion occurs.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## DiscreteTopology

The given topology equals the discrete topology, so every subset is open. Each natural-number coordinate has the canonical TopologicalSpace Nat = bottom and DiscreteTopology Nat instance. The product uses Pi.topologicalSpace, not the discrete topology on all sequences. Cylinders, rather than single sequences, form the domain basis.

Used by: BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## IsClopen

Both closed and open in the supplied topology. Conjunction of IsClosed and IsOpen; no compactness or disconnectedness replacement.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## interior

Largest open subset of a set. Union of all open subsets; compact interior emptiness forbids every nonempty open subset inside a compact set.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## ClusterPt

Every filter set meets every neighborhood of the point. Nontrivial meet of the neighborhood filter and the supplied filter; no deleted-point condition.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## IsCompact

Every open cover has a finite subcover. Literal filter-cluster-point definition; open-cover formulation is a proved equivalence, not definitional equality.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## TotallyBounded

Every positive metric scale has a finite ball cover. Literal entourage formulation; Metric.totallyBounded_iff is the proved metric equivalence used to force an infinite partition.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Homeomorph

A bijection continuous in both directions. Extends Equiv with continuous_toFun and continuous_invFun for the two supplied topologies.

Used by: BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Equiv

Functions in both directions with two inverse laws. No topology is supplied by Equiv; Homeomorph adds both continuity obligations.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Disjoint

For sets, intersection is empty. Literal lattice lower-bound definition; set disjointness is connected by a proved equivalence.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Pairwise

The binary relation holds for every pair of distinct indices. Excludes equal indices; nonempty disjoint children indexed bijectively by naturals give full distinct infinite branching.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.nonempty_homeomorph_iff.

## Function.Bijective

Injective and surjective. Two separate properties; opens plus continuity only produces a homeomorphism after both are proved.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Infinite

The type is not finite. Finite is the inductive class of equivalences to Fin n; do not infer infinity from a cover with repetitions.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Set.Finite

The subtype of elements of this set is a finite type. Finite class has an equivalence to some Fin n; finite_range uses the genuinely finite survivor-index subtype in the contradiction.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.ClopenScheme.image_cylinder, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.baire_hasClopenBasis, BaireCharacterization.baire_compactInteriorEmpty, BaireCharacterization.nonempty_homeomorph_iff.

## Denumerable

An encoding into naturals whose decoding reaches every natural. The constructor gives an actual equivalence with naturals; nonempty_equiv_of_countable uses countable plus Infinite to avoid repetitions.

Used by: BaireCharacterization.exists_clopen_partition, BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## CantorScheme.Disjoint

At each node, distinct children are disjoint. PiNat.res uses reverse prefixes a::l; disjoint siblings imply branch-limit injectivity.

Used by: BaireCharacterization.exists_clopen_scheme, BaireCharacterization.nonempty_homeomorph_of_completeSpace, BaireCharacterization.nonempty_homeomorph, BaireCharacterization.nonempty_homeomorph_iff.

## Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256 6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L112-L113

```lean
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L121-L123

```lean
/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

## Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

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

## Mathlib/Topology/MetricSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

SHA256 cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9

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

## Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

SHA256 13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35

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

## Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

SHA256 7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L95-L97

```lean
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  uniformity_basis_dist.totallyBounded_iff
```

## Mathlib/Topology/MetricSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

SHA256 9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618

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

## Mathlib/Topology/UniformSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256 0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c

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

## Mathlib/Topology/UniformSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

SHA256 68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L478-L482

```lean

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def TotallyBounded (s : Set α) : Prop :=
  ∀ d ∈ 𝓤 α, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, { x | (x, y) ∈ d }
```

## Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256 3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L271-L276

```lean
/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L288-L291

```lean
/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

## Mathlib/Topology/Neighborhoods.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

SHA256 ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a

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

## Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256 d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5

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

## Mathlib/Order/Filter/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

SHA256 5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb

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

## Mathlib/Order/Filter/Prod.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

SHA256 2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367

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

## Mathlib/Basic/ENNReal/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean

SHA256 211629947deb3d78a8541202d33a9fed3d4c8f22215daea3d7d37209a824d947

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean#L230-L231

```lean
/-- `ofReal x` returns `x` if it is nonnegative, `0` otherwise. -/
protected def ofReal (r : Real) : ℝ≥0∞ := r.toNNReal
```

## Mathlib/Order/Filter/Tendsto.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

SHA256 76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce

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

## Mathlib/Order/Filter/AtTopBot/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

SHA256 4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621

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

## Mathlib/Topology/Bornology/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

SHA256 427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e

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

## Mathlib/Topology/MetricSpace/Bounded.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

SHA256 dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b

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

## Mathlib/Topology/EMetricSpace/Diam.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean

SHA256 699ba791a149bdcdc24e9d7d650aa34925e04947d38df7e7c1ef9c9bd195822f

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

## Mathlib/Basic/Countable/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

SHA256 d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f

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

## Mathlib/Data/Set/Countable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

SHA256 047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L128-L135

```lean
/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective
```

## Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

SHA256 45e2fe2d79f14e9cf4e87f13f413eef94b418384fc3eaad3dce7b1a730ed54c9

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

## Mathlib/Topology/MetricSpace/Polish.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean

SHA256 71c9682ea53f194d1587fbd41695e35cc7fb8f51b1503f695ba4adfb15c52059

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

## Mathlib/Topology/Defs/Induced.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

SHA256 ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74

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

## Mathlib/Topology/Bases.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean

SHA256 fbd29cb53487d8ff54efda38cd831d4966a19a052654ef39a09352753986d1d6

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L811-L815

```lean
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, notMem_sdiff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).sdiff_empty⟩
  exacts [((countable_ofPred_finite_subset hb₁).image _).mono sdiff_subset, rfl]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L930-L941

```lean
/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets.
In particular, any open covering of `α` has a countable subcover: α is a Lindelöf space. -/
theorem isOpen_iUnion_countable [SecondCountableTopology α] {ι} (s : ι → Set α)
    (H : ∀ i, IsOpen (s i)) : ∃ T : Set ι, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i, s i := by
  let B := { b ∈ countableBasis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  have : Countable B := ((countable_countableBasis α).mono (sep_subset _ _)).to_subtype
  refine ⟨_, countable_range f, (iUnion₂_subset_iUnion _ _).antisymm (sUnion_subset ?_)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases (isBasis_countableBasis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩
```

## Mathlib/Topology/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256 2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L307-L311

```lean
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L578-L579

```lean
instance : TopologicalSpace ℕ := ⊥
instance : DiscreteTopology ℕ := ⟨rfl⟩
```

## Mathlib/Topology/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean

SHA256 47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f

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

## Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256 60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e

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

## Mathlib/Topology/MetricSpace/PiNat.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean

SHA256 a6d5b738f8217038bc1b2889f5fa0f0ea84b544dbc21761e90b35dcf8cd0d669

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L109-L110

```lean
def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L191-L193

```lean
def res (x : ℕ → α) : ℕ → List α
  | 0 => nil
  | Nat.succ n => x n :: res x n
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L195-L239

```lean
@[simp]
theorem res_zero (x : ℕ → α) : res x 0 = @nil α :=
  rfl

@[simp]
theorem res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = x n :: res x n :=
  rfl

@[simp]
theorem res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n := by induction n <;> simp [*]

/-- The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for all `m < n`. -/
theorem res_eq_res {x y : ℕ → α} {n : ℕ} :
    res x n = res y n ↔ ∀ ⦃m⦄, m < n → x m = y m := by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    | zero => simp
    | succ n ih =>
      simp only [res_succ, cons.injEq]
      refine ⟨h (Nat.lt_succ_self _), ih fun m hm => ?_⟩
      exact h (hm.trans (Nat.lt_succ_self _))

theorem res_injective : Injective (@res α) := by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

/-- `cylinder x n` is equal to the set of sequences `y` with the same restriction to `n` as `x`. -/
theorem cylinder_eq_res (x : ℕ → α) (n : ℕ) :
    cylinder x n = { y | res y n = res x n } := by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L344-L368

```lean
theorem isOpen_cylinder (x : ∀ n, E n) (n : ℕ) : IsOpen (cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _

theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s : Set (∀ n, E n) | ∃ (x : ∀ n, E n) (n : ℕ), s = cylinder x n } := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        ∃ v ∈ { S : Set (∀ i : ℕ, E i) | ∃ (U : ∀ i : ℕ, Set (E i)) (F : Finset ℕ),
          (∀ i : ℕ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℕ).pi U },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi fun n : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove F with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices ∀ i : ℕ, i ∈ F → y i ∈ U i by simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi
```

## Mathlib/Topology/MetricSpace/CantorScheme.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean

SHA256 49e509d69864b088f042d73153f4c33bdc3521a2f513306d55924a326d134246

```lean
/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L57-L58

```lean
noncomputable def inducedMap : Σ s : Set (ℕ → β), s → α :=
  ⟨{x | Set.Nonempty (⋂ n : ℕ, A (res x n))}, fun x => x.property.some⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L68-L69

```lean
def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a :: l)) ⊆ A l
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L119-L120

```lean
def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => Metric.ediam (A (res x n))) atTop (𝓝 0)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L77-L82

```lean
/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) := by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L137-L156

```lean

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_ofPred] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_val.isOpen_preimage
  apply isOpen_cylinder

/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L158-L184

```lean
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) := by
    have : Antitone fun n : ℕ => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    obtain ⟨n, hn⟩ := hdiam.dist_lt _ ε_pos x
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  use y
  rw [mem_iInter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_atTop]
  exact ⟨n.succ, umem _⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L71-L73

```lean
/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
protected def Disjoint : Prop :=
  ∀ l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))
```

## Mathlib/Basic/NNReal/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean

SHA256 5a94f78b3f6ce87106eea63ea8bfa48647de38cf2e51bff75f06a311ef821c99

```lean
/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L154-L156

```lean
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)
```

## Mathlib/Topology/Homeomorph/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean

SHA256 4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L42-L50

```lean
/-- Homeomorphism between `X` and `Y`, also called topological isomorphism -/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
```

## Mathlib/Logic/Equiv/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean

SHA256 c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L66-L77

```lean
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl
```

## Mathlib/Order/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

SHA256 5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c

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

## Mathlib/Logic/Pairwise.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean

SHA256 ccac95d1101a308ae38946e81caaa6d2c32e7e90ed99f7305dba9f01a955e62f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean#L33-L35

```lean
/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j
```

## Mathlib/Logic/Function/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Defs.lean

SHA256 a783ef2cbf8b63c895b371dfc43dec55fc07fee6bf0da23fa25cfbceab45a872

```lean
/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Defs.lean#L162-L164

```lean
/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
```

## Mathlib/Basic/Finite/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean

SHA256 1e94b38b09b4fc3acaff3c22f60ee46f960dd45ccc5392ca9993abbbb1ef8cad

```lean
/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean#L132-L136

```lean
/-- A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to
`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`. -/
class Infinite (α : Sort*) : Prop where
  /-- assertion that `α` is `¬Finite` -/
  not_finite : ¬Finite α
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean#L183-L185

```lean
/-- A set is finite if the corresponding `Subtype` is finite,
i.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`. -/
protected def Finite (s : Set α) : Prop := Finite s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Finite/Defs.lean#L101-L108

```lean
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _

theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩

theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h
```

## Mathlib/Basic/Denumerable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Denumerable.lean

SHA256 e18e96ba8a0e268f166fa57fa90a10afae862c7f5456b21e20b3df870fdb0fa7

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Denumerable.lean#L32-L35

```lean
/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Denumerable.lean#L322-L333

```lean
theorem nonempty_denumerable (α : Type*) [Countable α] [Infinite α] : Nonempty (Denumerable α) :=
  (nonempty_encodable α).map fun h => @Denumerable.ofEncodableOfInfinite _ h _

theorem nonempty_denumerable_iff {α : Type*} :
    Nonempty (Denumerable α) ↔ Countable α ∧ Infinite α :=
  ⟨fun ⟨_⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ nonempty_denumerable _⟩

instance nonempty_equiv_of_countable [Countable α] [Infinite α] [Countable β] [Infinite β] :
    Nonempty (α ≃ β) := by
  cases nonempty_denumerable α
  cases nonempty_denumerable β
  exact ⟨(Denumerable.eqv _).trans (Denumerable.eqv _).symm⟩
```

## Mathlib/Topology/Compactness/Compact.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean

SHA256 3fc7ffe7db4db0a2de07d6fdf0e65da486b3dced1f3bac4d58ab869a92f4ac64

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L384-L389

```lean
/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩
```

## Mathlib/Data/Set/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean

SHA256 21e4643bfcae089dbbca262cb9d4b4bad1ad1cd77adf31ae43f4d2f2ab69e492

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean#L32-L33

```lean
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
```

## Mathlib/Order/Disjointed.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjointed.lean

SHA256 9ba121f9b01633629f2b09e501aa72042135e488f1f3af9e14a66ae952d85719

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies, David Loeffler
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjointed.lean#L60-L62

```lean
unique function `g` having the same `partialSups` as `f` and such that `g i` and `g j` are
disjoint whenever `i < j`. -/
def disjointed (f : ι → α) (i : ι) : α := f i \ (Iio i).sup f
```

