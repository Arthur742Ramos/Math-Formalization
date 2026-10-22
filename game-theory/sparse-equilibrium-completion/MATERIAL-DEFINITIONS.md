# Material imported definitions at the exact Mathlib pin

The inventory records finite-index, interval, grid-size finite-dimensional recombination, compact-convex separation, and finite ordinal/prefix meanings. Ordinary ordered-real algebra, logical connectives, casts and function application remain background infrastructure. No imported game-feasibility or sparse-completion target is assumed. Game predicates are fixed public definitions. Finset.sum is generated from the retained Finset.prod/to_additive source and checked by finite_sum_literal. Module.rank uses irreducible_def; its retained macro source and the actual finite-product dimension law are explicit rather than presenting it as a textual def.

Classical Caratheodory recombination is Mathlib work by Johan Commelin and Kim Morrison, part of the Sphere Eversion project. The finite-dimensional affine cardinal bound is upstream infrastructure. Our proof preserves all selected hinge values exactly, rather than formalizing the paper's inequality-based extreme-point argument. No novelty claim is made for recombination.

The repository checker authenticates supported definition entries and all retained file/excerpt bytes. Generated declarations and precise theorem contracts have their own retained source and compiled bridges. Independent review owns inventory completeness and semantics; source hashes alone do not prove either.

The completion proof uses the classical compact/closed Hahn–Banach separation theorem from Mathlib (Yury Kudryashov and contributors). The explicit ordered skew matrix gives the separating support value. This is an existence proof over reals; it supplies no rational algorithm or complexity bound. StrongDual is retained as an abbreviation excerpt under ContinuousLinearMap.

## Fintype

A finite type has a finite duplicate-free enumeration containing every element. Finite sums range over that enumeration. Empty types are allowed.

Affected selected declarations: SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.block_support_card, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.prefix_exposing_identity, SparseCompletion.strict_prefix_rigidity, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.positive_target_full_support, SparseCompletion.bounded_two_anchor_minimum_share_rigidity

## Finset

A finite set is a multiset with no duplicate entries. Membership, complement and subset sums refer to the finite indexing set, without multiplicities.

Affected selected declarations: SparseCompletion.skew_weighted_sum, SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.compactCompletion_skew, SparseCompletion.compactCompletion_bounds, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.block_support_card, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.prefix_exposing_identity, SparseCompletion.strict_prefix_rigidity, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.positive_target_full_support, SparseCompletion.bounded_two_anchor_minimum_share_rigidity

## Finset.prod

Multiplicative source for the generated additive Finset.sum definition. The to_additive attribute generates Finset.sum as the mapped underlying multiset sum; finite_sum_literal checks that exact value.

Affected selected declarations: SparseCompletion.skew_weighted_sum, SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.block_support_card, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.prefix_exposing_identity, SparseCompletion.strict_prefix_rigidity, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.positive_target_full_support, SparseCompletion.bounded_two_anchor_minimum_share_rigidity

## Set.Icc

The closed interval consists of x with a ≤ x and x ≤ b. The grid/envelope domain includes both endpoints; interval_literal unfolds the actual predicate.

Affected selected declarations: SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion

## Nat.ceil

The natural ceiling delegates to FloorSemiring.ceil. FloorSemiring.gc_ceil says ceil a ≤ n iff a ≤ (n:ℝ); the natural ceiling is zero for negative a.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## FloorSemiring

Floor and ceiling operations with their natural-cast adjunction laws. The ceil field is a lower adjoint to the natural cast; natural_ceiling_meaning checks the resulting equivalence at ℝ.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## NNReal.sqrt

Nonnegative square root is the inverse order isomorphism of squaring on nonnegative reals. powOrderIso 2 supplies squaring; its inverse identities give a nonnegative root with square equal to the input.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Real.sqrt

The real square root applies NNReal.sqrt to Real.toNNReal. Negative inputs yield zero. Only nonnegative Mr/η is used; square_root_meaning proves the needed square and sign laws.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Real.toNNReal

Real-to-nonnegative-real conversion clips a real input below at zero. The underlying value is max r 0, with a proof of nonnegativity. For nonnegative inputs its coercion equals the original input.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Convex

Every point of the set is a star center of the set. Via StarConvex this means closure under nonnegative two-point real convex combinations; convex_literal proves the expanded quantifiers.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## StarConvex

All nonnegative combinations of a chosen center with a point of the set, with weights summing to one, remain in the set. Centers in the set quantify convexity. No topological closedness is assumed.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## convexHull

The closure operator generated by all convex supersets. Membership means belonging to every convex superset, proved by convex_hull_meaning. It is algebraic convex hull, not topological closure.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## AffineIndependent

Zero-sum finite affine relations with zero weighted subtraction have all coefficients zero. The point-subtraction base cancels when coefficient sum is zero. affine_independence_literal and weighted_subtraction_zero_sum audit the actual meaning.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Finset.weightedVSub

Finite weighted differences from a default affine base point. This is used only with zero total weight, where the base is arbitrary and cancels. The checked bridge specializes to vector-space base zero.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Finset.weightedVSubOfPoint

The linear map summing weights times differences from a specified base point. Its application is the literal finite sum; the zero-sum bridge verifies the needed base-zero interpretation.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## vectorSpan

The submodule spanned by all differences of two points in the set. vector_span_literal unfolds the pairwise-difference image; the dimension is at most that of the ambient feature space.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Submodule.span

The infimum of all submodules containing the supplied generating set. submodule_span_literal checks the precise intersection/infimum meaning; it is linear span, not an analytic closure.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Module.finrank

The natural-number conversion of the cardinal-valued module rank. Cardinal.toNat is zero on infinite cardinals. Here the feature space is a finite real product and the checked finite_feature_dimension law gives its actual finite dimension; no infinite-dimensional rank is interpreted as a support bound.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Finset.card

The number of elements in the underlying duplicate-free multiset. finite_card_literal checks this exact value. The support count is a count of original nonzero labels, not a count of distinct feature values.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.block_support_card, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.positive_target_full_support

## Fintype.card

The cardinality of the finite universal enumeration. type_card_literal checks its link to Finset.card. Empty finite feature types are allowed, giving the mass-only one-point case.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.block_support_card, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.positive_target_full_support

## IsCompact

Every nontrivial filter containing the set has a cluster point in the set. The filter is finer than the principal filter of s. ClusterPt means the neighborhood filter and input filter have nontrivial infimum; in finite Euclidean space this gives ordinary compactness.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## IsClosed

The complement is open. Closedness of the upper orthant is proved coordinatewise, rather than assumed. IsOpen is the given topology predicate.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Continuous

Preimages of open sets are open. Used for the image of a compact set under the weighted response linear map and for continuous separating functionals.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## LinearMap

A bundled additive scalar-preserving map. Specializing the scalar homomorphism to the identity on real numbers gives ordinary real linearity; weightedNegResponse is constructed with both laws.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## ContinuousLinearMap

A bundled linear map together with continuity. StrongDual real E abbreviates E to real continuous linear maps. Only evaluation, linearity and continuity are used, not any topology on the dual itself.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Set.image

The image comprises values of domain points in the specified set. weightedScoreSet is the image of the full bounded skew box. Membership yields an actual skew matrix with entry bounds, rather than an abstract unrelated score vector.

Affected selected declarations: SparseCompletion.cuts_weighted_completion, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.weighted_completion_iff, SparseCompletion.game_sparse_completion, SparseCompletion.exact_game_sparse_completion, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_exact_sparse_witness

## Finset.range

The finite set of natural numbers strictly less than n. Its underlying multiset is Multiset.range n, with a no-duplicates proof. mem_range states membership iff i<n.

Affected selected declarations: SparseCompletion.uniform_exposing_weight

## LocallyFiniteOrderBot

Finite lower order intervals with exact membership laws. Finset.Iio j consists of elements i<j. It is a finite set, distinct from a set-valued interval. On Fin m its cardinality is j.val.

Affected selected declarations: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight

## LocallyFiniteOrderTop

Finite upper order intervals with exact membership laws. This is the source class for the order-dual generated lower intervals. The actual lower interval uses LocallyFiniteOrderBot.finsetIio.

Affected selected declarations: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight

## Finset.Ioi

Source definition for order-dual generated Finset.Iio. The retained to_dual annotation generates Iio from Ioi by reversing the order. Actual Iio equality with the lower-interval field and membership i<j are independently compiled, not merely inferred from the source spelling.

Affected selected declarations: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight

## Retained source: Mathlib/Data/Fintype/Defs.lean

[Mathlib/Data/Fintype/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean)

Full-source SHA256: `e69e8e7a3605d293a7ef6c4a7aaefde3191da4f33b43b7be09963eec2e44965c`

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

### Fintype

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean#L51-L62)

```lean
variable {α β : Type*}

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

```

## Retained source: Mathlib/Data/Finset/Defs.lean

[Mathlib/Data/Finset/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean)

Full-source SHA256: `ac132a546c19ca9e9ec46f864faae346c2c613c8bd7123bb0807c4ad630c302d`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

### Finset

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean#L72-L79)

```lean
/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
@[use_set_notation_for_order, to_dual_dont_translate]
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val
```

## Retained source: Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

[Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean)

Full-source SHA256: `e935efa96ad9381658f3158f900d04589c46d7e933cab15f4d8632e1af85527f`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Finset.prod

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean#L59-L69)

```lean
/-- `∏ x ∈ s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`.

When the index type is a `Fintype`, the notation `∏ x, f x`, is a shorthand for
`∏ x ∈ Finset.univ, f x`. -/
@[to_additive /-- `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`.

When the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for
`∑ x ∈ Finset.univ, f x`. -/]
protected def prod [CommMonoid M] (s : Finset ι) (f : ι → M) : M :=
  (s.1.map f).prod
```

## Retained source: Mathlib/Order/Interval/Set/Defs.lean

[Mathlib/Order/Interval/Set/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean)

Full-source SHA256: `53970116254a7e705eb85f92c9236be431966dbd61c1c1315a914a6d05e39b7b`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

### Set.Icc

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L74-L81)

```lean
/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
@[to_dual self (reorder := a b)]
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

to_dual_insert_cast Icc := by simp only [and_comm]

@[simp, grind =, push, to_dual none] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := .rfl
@[to_dual none] theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl
```

## Retained source: Mathlib/Algebra/Order/Floor/Defs.lean

[Mathlib/Algebra/Order/Floor/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean)

Full-source SHA256: `f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

### Nat.ceil

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L115-L122)

```lean

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil
```

### FloorSemiring

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L57-L71)

```lean
/-- A `FloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. Please see the above `TODO`. -/
class FloorSemiring (α) [Semiring α] [PartialOrder α] where
  /-- `FloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α → ℕ
  /-- `FloorSemiring.ceil a` computes the least natural `n` such that `a ≤ (n : α)`. -/
  ceil : α → ℕ
  /-- `FloorSemiring.floor` of a negative element is zero. -/
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- A natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion to `α` is
  smaller than `a`. -/
  gc_floor {a : α} {n : ℕ} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  /-- `FloorSemiring.ceil` is the lower adjoint of the coercion `↑ : ℕ → α`. -/
  gc_ceil : GaloisConnection ceil (↑)
```

## Retained source: Mathlib/Analysis/Real/Sqrt.lean

[Mathlib/Analysis/Real/Sqrt.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean)

Full-source SHA256: `f4e96c735ead60a8983bcf8eb6e38dfd05d8102c3f741094f73639858605bb6a`

```lean
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
```

### NNReal.sqrt

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L40-L51)

```lean
namespace NNReal

variable {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot]
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero

@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _

@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x ^ 2) = x := sqrt.apply_symm_apply _
```

### Real.sqrt

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L108-L113)

```lean

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

## Retained source: Mathlib/Basic/NNReal/Defs.lean

[Mathlib/Basic/NNReal/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean)

Full-source SHA256: `5a94f78b3f6ce87106eea63ea8bfa48647de38cf2e51bff75f06a311ef821c99`

```lean
/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

### Real.toNNReal

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L154-L159)

```lean
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)

theorem _root_.Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
```

## Retained source: Mathlib/Analysis/Convex/Basic.lean

[Mathlib/Analysis/Convex/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Basic.lean)

Full-source SHA256: `9044a0be27a288e404cbd80670eb0e739271be1fdd7577dbf205dff40af24fcf`

```lean
/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
```

### Convex

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Basic.lean#L48-L54)

```lean

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

```

## Retained source: Mathlib/Analysis/Convex/Star.lean

[Mathlib/Analysis/Convex/Star.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Star.lean)

Full-source SHA256: `7d8a7df5d59812e6d1bebdeb0cfddc109fb5a54b0973eff14c128af0ff933858`

```lean
/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
```

### StarConvex

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Star.lean#L70-L75)

```lean
/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

```

## Retained source: Mathlib/Analysis/Convex/Hull.lean

[Mathlib/Analysis/Convex/Hull.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Hull.lean)

Full-source SHA256: `7f05ca2487110c7a2e35be41043231e1094e78e7dc34045202d4b0c85913e53b`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
```

### convexHull

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Hull.lean#L44-L62)

```lean
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
@[simps! isClosed]
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter

variable (s : Set E)

theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s

theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) := (convexHull 𝕜).isClosed_closure s

set_option backward.isDefEq.respectTransparency false in
theorem convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

variable {𝕜 s} {t : Set E} {x y : E}

theorem mem_convexHull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]
```

## Retained source: Mathlib/LinearAlgebra/AffineSpace/Independent.lean

[Mathlib/LinearAlgebra/AffineSpace/Independent.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Independent.lean)

Full-source SHA256: `9475bae0945645d79cc089bb3eeee405e6fae6d6923c8f22e6686b3a53219594`

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

### AffineIndependent

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Independent.lean#L50-L61)

```lean
/-- An indexed family is said to be affinely independent if no nontrivial weighted subtractions
(where the sum of weights is 0) are 0. -/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k),
    ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0

/-- `AffineIndepOn k p s` states that the points in the family `p` that are indexed
by the elements of `s` are affinely independent over `k`. -/
def AffineIndepOn (p : ι → P) (s : Set ι) : Prop := AffineIndependent k (fun x : s ↦ p x)

/-- The definition of `AffineIndependent`. -/
theorem affineIndependent_def (p : ι → P) :
```

## Retained source: Mathlib/LinearAlgebra/AffineSpace/Combination.lean

[Mathlib/LinearAlgebra/AffineSpace/Combination.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean)

Full-source SHA256: `d7c58df194c17fb81cc55d9f20b4cd0aaef1b06695b434594e2c97b51c16f1a8`

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

### Finset.weightedVSub

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean#L227-L249)

```lean
/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weightedVSub (p : ι → P) : (ι → k) →ₗ[k] V :=
  s.weightedVSubOfPoint p (Classical.choice S.nonempty)

/-- Applying `weightedVSub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weightedVSub` would involve selecting a preferred base point with
`weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` and then
using `weightedVSubOfPoint_apply`. -/
theorem weightedVSub_apply (w : ι → k) (p : ι → P) :
    s.weightedVSub p w = ∑ i ∈ s, w i • (p i -ᵥ Classical.choice S.nonempty) := by
  simp [weightedVSub]

/-- `weightedVSub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w :=
  s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

```

### Finset.weightedVSubOfPoint

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean#L58-L68)

```lean
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weightedVSubOfPoint (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
  ∑ i ∈ s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]
theorem weightedVSubOfPoint_apply (w : ι → k) (p : ι → P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i ∈ s, w i • (p i -ᵥ b) := by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]
```

## Retained source: Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean

[Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean)

Full-source SHA256: `db1a84f71e149014ac383885710a49afa0d625a144e776757fff81c1cc923981`

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

### vectorSpan

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean#L62-L68)

```lean
/-- The submodule spanning the differences of a (possibly empty) set of points. -/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/-- The definition of `vectorSpan`, for rewriting. -/
theorem vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl
```

## Retained source: Mathlib/LinearAlgebra/Span/Defs.lean

[Mathlib/LinearAlgebra/Span/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean)

Full-source SHA256: `a0403eb6f96f384672a7b52d7ddb94405d3d3b1c43f699facc3e99ef8b0c00c6`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### Submodule.span

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean#L43-L48)

```lean

variable (R) in
/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }

```

## Retained source: Mathlib/LinearAlgebra/Dimension/Finrank.lean

[Mathlib/LinearAlgebra/Dimension/Finrank.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean)

Full-source SHA256: `4ab91c2b2e2d56f24c0260f25d55a31042cac8112a943a7c877594528c363e21`

```lean
/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
```

### Module.finrank

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L54-L64)

```lean
For a general module `M` over a ring `R`, `Module.finrank R M` is defined to be the supremum of the
cardinalities of the `R`-linearly independent subsets of `M`, if this supremum is finite. It is
defined by convention to be `0` if this supremum is infinite. See `Module.rank` for a
cardinal-valued version where infinite rank modules have rank an infinite cardinal.

Note that if `R` is not a field then there can exist modules `M` with `¬(Module.Finite R M)` but
`finrank R M ≠ 0`. For example `ℚ` has `finrank` equal to `1` over `ℤ`, because the nonempty
`ℤ`-linearly independent subsets of `ℚ` are precisely the nonzero singletons. -/
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)

```

## Retained source: Mathlib/Data/Finset/Card.lean

[Mathlib/Data/Finset/Card.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean)

Full-source SHA256: `901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```

### Finset.card

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L43-L53)

```lean

/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

theorem card_def (s : Finset α) : #s = Multiset.card s.1 :=
  rfl
```

## Retained source: Mathlib/Data/Fintype/Card.lean

[Mathlib/Data/Fintype/Card.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean)

Full-source SHA256: `a77eb573a459ee525cfb4ac753dd05968ef2cc831d7549dc4e9036c7a90a1f00`

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

### Fintype.card

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean#L39-L43)

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
```

## Retained source: Mathlib/Analysis/Convex/Caratheodory.lean

[Mathlib/Analysis/Convex/Caratheodory.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Caratheodory.lean)

Full-source SHA256: `8e2ead25535366604c2caab3071e5549586f909fe70b885d1c75784e117720f2`

```lean
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
```

### Caratheodory-contract

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Caratheodory.lean#L148-L166)

```lean
/-- **Carathéodory's convexity theorem** -/
theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert! Set.iUnion_subset _; intro
    exact convexHull_mono ‹_›

/-- A more explicit version of `convexHull_eq_union`. -/
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜), Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
```

## Retained source: Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean

[Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean)

Full-source SHA256: `d1762f0257b80394b1d08f2cc68ad42c8723d5f6aefbcf7ce9e89a22a82eb864`

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

### AffineIndependent-card-bound

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean#L313-L321)

```lean
variable {k}

lemma AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι → P} (hp : AffineIndependent k p) :
    Fintype.card ι ≤ Module.finrank k (vectorSpan k (Set.range p)) + 1 := by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp
```

## Retained source: Mathlib/LinearAlgebra/Dimension/Basic.lean

[Mathlib/LinearAlgebra/Dimension/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Basic.lean)

Full-source SHA256: `f1989e361485382c4a47a8712dbdd58a7c89b339788b7d75c0dac0d9a3a5f12f`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
```

### Module.rank-source

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Basic.lean#L59-L72)

```lean
(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

See also `Module.finrank` for a `ℕ`-valued function which returns the correct value
for a finite-dimensional vector space (but 0 for an infinite-dimensional vector space).
-/
@[stacks 09G3 "first part"]
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndepOn R id s }, (#ι.1)

theorem rank_le_card : Module.rank R M ≤ #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)
```

## Retained source: Mathlib/LinearAlgebra/Dimension/Constructions.lean

[Mathlib/LinearAlgebra/Dimension/Constructions.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Constructions.lean)

Full-source SHA256: `ba705b4a5e12709dfbd792ddd9946aafdcc276daf1a8778de760ec2f4e660363`

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen
-/
```

### finite-product-dimension

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Constructions.lean#L287-L293)

```lean

/-- The `finrank` of `(ι → R)` is `Fintype.card ι`. -/
theorem Module.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι → R) = Fintype.card ι := by
  simp [finrank]

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
```

## Retained source: Mathlib/Topology/Defs/Filter.lean

[Mathlib/Topology/Defs/Filter.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean)

Full-source SHA256: `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### IsCompact

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L288-L291)

```lean
/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

### ClusterPt

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L273-L276)

```lean
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

## Retained source: Mathlib/Topology/Defs/Basic.lean

[Mathlib/Topology/Defs/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean)

Full-source SHA256: `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### IsClosed

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L105-L109)

```lean
/-- A set is closed if its complement is open -/
@[wikidata Q320357]
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

### Continuous

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L152-L158)

```lean
/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
@[fun_prop, wikidata Q170058]
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## Retained source: Mathlib/Algebra/Module/LinearMap/Defs.lean

[Mathlib/Algebra/Module/LinearMap/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean)

Full-source SHA256: `aea1c354ffc798aaa5397f2f58124bc2ed7b29d24227ae568d3f5745f839570d`

```lean
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
```

### LinearMap

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/LinearMap/Defs.lean#L79-L88)

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

```

## Retained source: Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean

[Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean)

Full-source SHA256: `d081051ca12363eeb95590a88decc17fd18f5bdc76c7fb30748f48ffc854d379`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

### ContinuousLinearMap

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L56-L65)

```lean

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

```

### StrongDual

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L92-L97)

```lean

/-- The *strong dual* of a topological vector space `M` over a ring `R`. This is the space of
continuous linear functionals and is equipped with the topology of uniform convergence
on bounded subsets. `StrongDual R M` is an abbreviation for `M →L[R] R`. -/
abbrev StrongDual (R : Type*) [Semiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] : Type _ := M →L[R] R
```

## Retained source: Mathlib/Data/Set/Defs.lean

[Mathlib/Data/Set/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean)

Full-source SHA256: `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

### Set.image

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L265-L266)

```lean
`f a = b` for some `a ∈ s`. -/
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
```

## Retained source: Mathlib/Analysis/LocallyConvex/Separation.lean

[Mathlib/Analysis/LocallyConvex/Separation.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/LocallyConvex/Separation.lean)

Full-source SHA256: `649cfe33fdb3999dfe168ee52cdfba11c45856e3fc34f7be4f971c80c772166e`

```lean
/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
```

### compact_closed_separation

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/LocallyConvex/Separation.lean#L196-L214)

```lean
/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s)
    (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨0, -2, -1, by simp⟩
  obtain rfl | _ht := t.eq_empty_or_nonempty
  · exact ⟨0, 1, 2, by simp⟩
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_isMaxOn hs f.continuous.continuousOn
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u,
      fun a ha => by have := hx₂ ha; dsimp at this; linarith,
      by linarith,
      fun b hb => hf₂ b (tV hb)⟩

```

## Retained source: Mathlib/Data/Finset/Range.lean

[Mathlib/Data/Finset/Range.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Range.lean)

Full-source SHA256: `558338b4d2aafb16975268881803408ffa50d44abc7b9d9eee418e1590094576`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

### Finset.range

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Range.lean#L52-L65)

```lean
/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩

@[simp]
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl

@[simp] lemma _root_.Multiset.toFinset_range (n : ℕ) : (Multiset.range n).toFinset = .range n :=
  Finset.val_injective (Finset.range n).nodup.dedup

@[simp, grind =]
theorem mem_range : m ∈ range n ↔ m < n :=
  Multiset.mem_range
```

## Retained source: Mathlib/Order/Interval/Finset/Defs.lean

[Mathlib/Order/Interval/Finset/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean)

Full-source SHA256: `023c4216dc4c48cc0a97e5ceb876aa54e1db126b19097ee89c4d3b12059970a8`

```lean
/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
```

### LocallyFiniteOrderBot

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean#L156-L167)

```lean
/-- This mixin class describes an order where all intervals bounded above are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderBot` as it allows empty types. -/
@[to_dual]
class LocallyFiniteOrderBot (α : Type*) [Preorder α] where
  /-- Left-infinite right-open interval -/
  finsetIio : α → Finset α
  /-- Left-infinite right-closed interval -/
  finsetIic : α → Finset α
  /-- `x ∈ finsetIic a ↔ x ≤ a` -/
  finset_mem_Iic : ∀ a x : α, x ∈ finsetIic a ↔ x ≤ a
  /-- `x ∈ finsetIio a ↔ x < a` -/
  finset_mem_Iio : ∀ a x : α, x ∈ finsetIio a ↔ x < a
```

### LocallyFiniteOrderTop

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean#L141-L154)

```lean
  finset_mem_Ioc := by grind
  finset_mem_Ioo := by grind

/-- This mixin class describes an order where all intervals bounded below are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderTop` as it allows empty types. -/
class LocallyFiniteOrderTop (α : Type*) [Preorder α] where
  /-- Left-open right-infinite interval -/
  finsetIoi : α → Finset α
  /-- Left-closed right-infinite interval -/
  finsetIci : α → Finset α
  /-- `x ∈ finsetIci a ↔ a ≤ x` -/
  finset_mem_Ici : ∀ a x : α, x ∈ finsetIci a ↔ a ≤ x
  /-- `x ∈ finsetIoi a ↔ a < x` -/
  finset_mem_Ioi : ∀ a x : α, x ∈ finsetIoi a ↔ a < x
```

### Finset.Ioi

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean#L360-L372)

```lean
/-- The finset $(a, ∞)$ of elements `x` such that `a < x`. Basically `Set.Ioi a` as a finset. -/
@[to_dual
/-- The finset $(-∞, b)$ of elements `x` such that `x < b`. Basically `Set.Iio b` as a finset. -/]
def Ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a

@[to_dual (attr := simp, grind =)]
theorem mem_Ici : x ∈ Ici a ↔ a ≤ x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _

@[to_dual (attr := simp, grind =)]
theorem mem_Ioi : x ∈ Ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _
```

## Retained source: Mathlib/Order/Interval/Finset/Fin.lean

[Mathlib/Order/Interval/Finset/Fin.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Fin.lean)

Full-source SHA256: `1f61a87f5a33679269110a3da98111b222e2daecb73418b7b7df64238cf98263`

```lean
/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
```

### Fin.card_Iio

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Fin.lean#L887-L891)

```lean
@[simp]
theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]

@[simp]
theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]
```

## Retained source: Mathlib/Data/Fintype/BigOperators.lean

[Mathlib/Data/Fintype/BigOperators.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean)

Full-source SHA256: `b9a6354ebff5fcd22fb1ddb7992682a404ec44c8ee42d519177f17d1d5a239e9`

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

### Fin.sum_range_conversion

[Exact excerpt](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean#L225-L232)

```lean
/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive /-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/]
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i : Fin n, f i = ∏ i ∈ range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x ∈ range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i ∈ range n, f i := by rw [← attach_eq_univ, prod_attach]
```

## Lean core finite ordinal

Fin n is a natural value with a proof that it is strictly smaller than n. Fin.ext identifies elements with equal values. The canonical finite ordinal includes no labels outside that bound. GitHub fetch_file at exact compiler commit independently returned the same whole-file Git blob SHA; installed compiler source bytes match.

[Exact compiler source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean)

Full-source SHA256: `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`; Git blob `f87ee970af5149d74434f09a89aedff1a8fdb2d2`.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

```lean

In particular, a `Fin n` is a natural number `i` with the constraint that `i < n`. It is the
canonical type with `n` elements.
-/
@[pp_using_anonymous_constructor]
structure Fin (n : Nat) where
  /-- Creates a `Fin n` from `i : Nat` and a proof that `i < n`. -/
  mk ::
  /--
  The number that is strictly less than `n`.

  `Fin.val` is a coercion, so any `Fin n` can be used in a position where a `Nat` is expected.
  -/
  val  : Nat
  /--
  The number `val` is strictly less than the bound `n`.
  -/
  isLt : LT.lt val n

attribute [coe] Fin.val
```

## Quantitative support and attained-minimum meanings

### Nat.find

Least natural satisfying a predicate known to have a witness. Projects Nat.findX. Our support predicate uses actual real strategies and matrices; classical decidability is noncomputable, with no claimed executable decision algorithm. The dense exact witness proves nonemptiness for nonnegative tolerance.

Affected selected declarations: SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp

### Nat.findX

Witness of the predicate together with failure at every smaller natural. WellFounded.fix scans successive naturals under the decreasing relation lbp, whose well-foundedness follows from the supplied existential witness. The DecidablePred parameter is genuine standard classical choice in this noncomputable use.

Affected selected declarations: SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp

### RelEmbedding

An injective map reflecting and preserving the specified relation. OrderEmbedding abbreviates RelEmbedding of the two less-than-or-equal relations. On linear orders this yields strict monotonicity; no equal grid indices are introduced by finite enumeration.

Affected selected declarations: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp

### Finset.orderIsoOfFin

Increasing bijection from Fin k to a finite ordered set s of cardinality k. Constructed from the sorted list, the Fin cardinality cast and a subtype order isomorphism; it covers every element of s.

Affected selected declarations: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp

### Finset.orderEmbOfFin

Increasing injection from Fin k into the ambient linear order, enumerating exactly s. Composes the finite-set order isomorphism with subtype inclusion. map_orderEmbOfFin_univ gives full coverage; no contiguity of the finite subset is assumed.

Affected selected declarations: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp

Existing finite enumeration, sums, cardinality and natural-range meanings also occur in: SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.two_anchor_total_support_card, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp. Real square-root sign/square meanings additionally occur in the quantitative lower and sharp support laws.

### Nat.find pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Find.lean

Whole-source SHA256: 5a07ff428d4fbd44e2921e630dce57685bc1a1ff544360a7109175aba9fc2640

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Find.lean#L55-L79

```lean

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.
-/
protected def find : ℕ :=
  (Nat.findX H).1

protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  Nat.le_of_not_gt fun l => Nat.find_min H l h
```

### Nat.findX pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Find.lean

Whole-source SHA256: 5a07ff428d4fbd44e2921e630dce57685bc1a1ff544360a7109175aba9fc2640

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Find.lean#L25-L53

```lean

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

private theorem wf_lbp (H : ∃ n, p n) : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

variable [DecidablePred p] (H : ∃ n, p n)

/-- Find the smallest `n` satisfying `p n`. Returns a subtype. -/
protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
```

### RelEmbedding pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/RelIso/Basic.lean

Whole-source SHA256: f137f96d298cd198b1db89326bc0967417db4eb66abc752f8bc71d9a9a6428b1

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/RelIso/Basic.lean#L201-L205

```lean
/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure RelEmbedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β where
  /-- Elements are related iff they are related after apply a `RelEmbedding` -/
  map_rel_iff' : ∀ {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b
```

### OrderEmbedding-abbreviation pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Hom/Basic.lean

Whole-source SHA256: e23a4af92ee1e161b8511356b2ae57cf4d860cfc96cd5bdbfa7ee765499ace15

```lean
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Hom/Basic.lean#L91-L94

```lean
/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelEmbedding (≤) (≤)`. -/
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)
```

### Finset.orderIsoOfFin pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean

Whole-source SHA256: 2fd791b340659c85aea7c548aa01c61e9b73f02bc68346e2eb22b53cc9a1ec4d

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean#L181-L189

```lean

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOfFin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.castOrderIso ((s.length_sort (· ≤ ·)).trans h).symm) <|
    (s.sortedLT_sort.getIso _).trans <| Set.orderIsoOfEq {x | x ∈ s.sort (· ≤ ·)} _ <| by simp

```

### Finset.orderEmbOfFin pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean

Whole-source SHA256: 2fd791b340659c85aea7c548aa01c61e9b73f02bc68346e2eb22b53cc9a1ec4d

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean#L190-L195

```lean
/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOfFin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `Fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)
```

### sorted-enumeration-coverage pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean

Whole-source SHA256: 2fd791b340659c85aea7c548aa01c61e9b73f02bc68346e2eb22b53cc9a1ec4d

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sort.lean#L209-L232

```lean

@[simp]
theorem orderEmbOfFin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2

@[simp]
theorem range_orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ → α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.coe_subtype, OrderIso.coe_toOrderEmbedding,
    Subtype.range_coe_subtype, Finset.setOfPred_mem]

@[simp]
theorem image_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.image (s.orderEmbOfFin h) Finset.univ = s := by
  apply Finset.coe_injective
  simp

@[simp]
theorem map_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.map (s.orderEmbOfFin h).toEmbedding Finset.univ = s := by
  simp [map_eq_image]
```

### cubic-Jensen-contract pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Chebyshev.lean

Whole-source SHA256: ad0178d8901043bbf10bb55b9a3b689924d470f626b76527bef1e46b42654063

```lean
/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Chebyshev.lean#L126-L128

```lean
/-- Special case of **Jensen's inequality** for sums of powers. -/
lemma pow_sum_le_card_mul_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∀ n, (∑ i ∈ s, f i) ^ (n + 1) ≤ (#s : α) ^ n * ∑ i ∈ s, f i ^ (n + 1)
```


Nat.find and Nat.findX are unexposed upstream definitions. The independent bridge modules prove their projection equality from minimality and attainment; this is a proved equality, not claimed cross-module definitional equality.
