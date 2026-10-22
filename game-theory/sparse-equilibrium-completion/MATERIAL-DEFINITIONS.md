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

The real square root applies NNReal.sqrt to Real.toNNReal. Negative inputs yield zero. Nonnegative radicands include Mr/η, ε, ε+δ, ε+3δ/8 and 3/1216 under the selected contracts' positivity hypotheses; square_root_meaning proves the needed square and sign laws.

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

## Residual minima and interval lower bounds

The existing finite enumeration, sums and cardinality meanings support the new game and support contracts: SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_origin.

The scalar SparseCompletion.residual_rate_from_inverse_square uses the existing Real.sqrt, NNReal.sqrt and Real.toNNReal meanings. SparseCompletion.clipped_observation_interval uses Set.Icc and ordinary real order; both independent bridge modules check the clipped-interval equivalence. SparseCompletion.block_entry_perturbation uses arbitrary index types without finite enumeration.

Nat.find/findX attainment and minimality additionally support the new interval/core support minima and residual minima inherited from the total minimum. The dense witness-existence lemmas uniform_interval_support_exists and uniform_core_support_exists precede Nat.find and do not themselves use a natural minimum. The existing square-root meanings apply to the new positive effective-tolerance rates. No uncertainty upper theorem is assumed.

## Explicit bin construction and sharp uncertainty laws

### Equiv

A map equipped with a two-sided inverse. Injectivity and surjectivity follow from the inverse laws; no omitted or duplicate original labels enter the canonical bin partition. Equiv.Perm is the self-equivalence abbreviation.

Affected selected declarations: SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp

### finSigmaFinEquiv

Bijection from disjoint finite fibers indexed by Fin h to the ordinal of their total length. Its value is the sum of preceding bin lengths plus the local label. Dependent pairs record a bin and a label within that bin; the inverse covers each original label exactly once.

Affected selected declarations: SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp

### Finset.sigma

Finite set of dependent pairs whose first label belongs to s and second label to the corresponding fiber. The no-duplicates proof combines the outer and fiber no-duplicates laws. Sigma.instFintype enumerates all bins/fiber labels using univ.sigma univ, and the generated sum_sigma contract sums exactly once over each pair.

Affected selected declarations: SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp

### Fin.revPerm

The reversal permutation of a finite ordinal. Fin.rev maps i to n-(i+1). It is an involution. The exact compiler source for this value is separately authenticated; reversal only pairs uniform-bin terms and never changes the original-label repertoire.

Affected selected declarations: SparseCompletion.bin_pair_call_le, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_call_compression, SparseCompletion.bin_compressed_nonneg, SparseCompletion.bin_compressed_mass, SparseCompletion.bin_compressed_support, SparseCompletion.bin_compressed_moment, SparseCompletion.bin_compressed_affine_moment, SparseCompletion.bin_compressed_calls, SparseCompletion.bin_compressed_quadratic_loss, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp

Existing finite enumeration/sums/cardinality and real square-root meanings additionally support these bin/support/uncertainty contracts: SparseCompletion.inner_pair_call_le, SparseCompletion.bin_middle_sum, SparseCompletion.bin_middle_order, SparseCompletion.bin_middle_outer, SparseCompletion.bin_pair_call_le, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.negative_call_identity, SparseCompletion.bin_call_compression, SparseCompletion.bin_middle_sum_real, SparseCompletion.bin_affine_mean, SparseCompletion.bin_quadratic_loss_identity, SparseCompletion.bin_middle_gap_bound, SparseCompletion.bin_quadratic_loss_bounds, SparseCompletion.bin_compressed_nonneg, SparseCompletion.bin_compressed_mass, SparseCompletion.bin_compressed_support, SparseCompletion.bin_compressed_moment, SparseCompletion.bin_compressed_affine_moment, SparseCompletion.bin_compressed_calls, SparseCompletion.bin_compressed_quadratic_loss, SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.balancedLength_positive, SparseCompletion.balancedLength_mass, SparseCompletion.balancedLength_bound, SparseCompletion.balancedLength_cube_sum, SparseCompletion.uniform_score_affine, SparseCompletion.uniform_target_cuts, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.bin_error_scale, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.two_core_anchor_shift, SparseCompletion.core_observation_adjustment, SparseCompletion.uniform_core_adjust, SparseCompletion.double_grid_support_upper, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.core_witness_interval, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uncertainty_rate_comparison, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp. Scalar inner_pair_call_le, negative_call_identity, bin_error_scale, core_observation_adjustment and uncertainty_rate_comparison have no finite-index assumptions; the last comparison uses real square roots. Nat.find is used only by attained support-minimum sharp laws in this tranche.

### Equiv pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean

Whole-source SHA256: c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L65-L78

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

### Equiv.Perm-abbreviation pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean

Whole-source SHA256: c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L95-L97

```lean
/-- `Perm α` is the type of bijections from `α` to itself. -/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α
```

### finSigmaFinEquiv pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Fin.lean

Whole-source SHA256: 7f5fb55b9f917df705f1861452ada2108b4dbaac92e7368aaf2f9ade293812d6

```lean
/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Fin.lean#L678-L692

```lean
/-- Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. -/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  match m with
  | 0 => @Equiv.equivOfIsEmpty _ _ _ (by simp)
  | Nat.succ m =>
    calc _ ≃ _ := (@finSumFinEquiv m 1).sigmaCongrLeft.symm
      _ ≃ _ := Equiv.sumSigmaDistrib _
      _ ≃ _ := finSigmaFinEquiv.sumCongr (Equiv.uniqueSigma _)
      _ ≃ _ := finSumFinEquiv
      _ ≃ _ := finCongr (Fin.sum_univ_castSucc n).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) + k.2 := by
```

### Finset.sigma pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sigma.lean

Whole-source SHA256: 20fcd45319167bd06399a6e801084cf1673b36d66a8a4242017ccb892d05a185

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sigma.lean#L44-L52

```lean
/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : Finset (Σ i, α i) :=
  ⟨_, s.nodup.sigma fun i => (t i).nodup⟩

variable {s s₁ s₂ t t₁ t₂}

@[simp, grind =]
theorem mem_sigma {a : Σ i, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 :=
  Multiset.mem_sigma
```

### finite-dependent-enumeration pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sigma.lean

Whole-source SHA256: bcdc1fabf19ac926c1b614c8b16cf6f58813f38ef865a4da51e717bc96da8045

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sigma.lean#L37-L41

```lean

instance Sigma.instFintype : Fintype (Σ i, κ i) := ⟨univ.sigma fun _ ↦ univ, by simp⟩
instance PSigma.instFintype : Fintype (Σ' i, κ i) := .ofEquiv _ (Equiv.psigmaEquivSigma _).symm

@[simp] lemma Finset.univ_sigma_univ : univ.sigma (fun _ ↦ univ) = (univ : Finset (Σ i, κ i)) := rfl
```

### finite-dependent-sum pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean

Whole-source SHA256: b9a6354ebff5fcd22fb1ddb7992682a404ec44c8ee42d519177f17d1d5a239e9

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean#L142-L159

```lean
/-- Product over a sigma type equals the repeated product.

This is a version of `Finset.prod_sigma` specialized to the case
of multiplication over `Finset.univ`. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum.

This is a version of `Finset.sum_sigma` specialized to the case of summation over `Finset.univ`. -/]
theorem prod_sigma {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : Sigma α → M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩ :=
  Finset.prod_sigma ..

/-- Product over a sigma type equals the repeated product, curried version.
This version is useful to rewrite from right to left. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum, curried version.
This version is useful to rewrite from right to left. -/]
theorem prod_sigma' {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : (i : ι) → α i → M) : ∏ x : Sigma α, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  prod_sigma ..
```

### Fin.revPerm pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fin/Rev.lean

Whole-source SHA256: d4633da3d0c9050d365ee369fbc414ee2be342d7963f9d84b71f4a9863a18a1e

```lean
/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Joel Riou, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fin/Rev.lean#L32-L38

```lean
theorem rev_involutive : Involutive (rev : Fin n → Fin n) := rev_rev

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
@[simps! apply]
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm rev rev_involutive
```

### finite-permutation-sum pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

Whole-source SHA256: e935efa96ad9381658f3158f900d04589c46d7e933cab15f4d8632e1af85527f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean#L745-L751

```lean
@[to_additive]
lemma _root_.Function.Bijective.prod_comp {e : ι → κ} (he : e.Bijective) (g : κ → M) :
    ∏ i, g (e i) = ∏ i, g i := prod_bijective _ he _ _ fun _ ↦ rfl

@[to_additive]
lemma _root_.Equiv.prod_comp (e : ι ≃ κ) (g : κ → M) : ∏ i, g (e i) = ∏ i, g i :=
  prod_equiv e _ _ fun _ ↦ rfl
```

### Compiler Fin.rev

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Fin/Basic.lean

Whole-source SHA256: bb3d4e46cb40a24f5a09e6e003c76f2b84140a598df81233f0bffe3afe08cbf4

GitHub returned this exact whole-file blob at the pinned compiler commit: 6fee3ab2eaacf1b76de02ea7f7880f29fbac8294. Reversal of ordinal i has natural value n-(i+1), remains within n and is involutive.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Robert Y. Lewis, Keeley Hoek, Mario Carneiro
-/
```

```lean
Replaces a value with its difference from the largest value in the type.

Considering the values of `Fin n` as a sequence `0`, `1`, …, `n-2`, `n-1`, `Fin.rev` finds the
corresponding element of the reversed sequence. In other words, it maps `0` to `n-1`, `1` to `n-2`,
..., and `n-1` to `0`.

Examples:
 * `(5 : Fin 6).rev = (0 : Fin 6)`
 * `(0 : Fin 6).rev = (5 : Fin 6)`
 * `(2 : Fin 5).rev = (2 : Fin 5)`
-/
@[inline, implicit_reducible] def rev (i : Fin n) : Fin n := ⟨n - (i + 1), Nat.sub_lt i.pos (Nat.succ_pos _)⟩
```

### Compiler Sigma

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Core.lean

Whole-source SHA256: 264a0b48fedc91fadf55fc5caac8d91003e3908a6e5e42736e2ac8bf1f7cdf99

GitHub returned this exact whole-file blob at the pinned compiler commit: 23e784c3806badcabd1e8f19c50946d66bc3c87a. Dependent pair has first component in alpha and second component in the fiber beta of that first component.

```lean
/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
```

```lean
Dependent pairs, in which the second element's type depends on the value of the first element. The
type `Sigma β` is typically written `Σ a : α, β a` or `(a : α) × β a`.

Although its values are pairs, `Sigma` is sometimes known as the *dependent sum type*, since it is
the type level version of an indexed summation.
-/
@[pp_using_anonymous_constructor]
structure Sigma {α : Type u} (β : α → Type v) where
  /--
  Constructs a dependent pair.

  Using this constructor in a context in which the type is not known usually requires a type
  ascription to determine `β`. This is because the desired relationship between the two values can't
  generally be determined automatically.
  -/
  mk ::
  /--
  The first component of a dependent pair.
  -/
  fst : α
  /--
  The second component of a dependent pair. Its type depends on the first component.
  -/
  snd : β fst

attribute [unbox] Sigma
```


The retained Equiv inverse and ordinal-reversal contracts additionally support SparseCompletion.balanced_game_witness, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_calls, SparseCompletion.binned_call_contraction, SparseCompletion.binned_game_witness, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.partition_game_witness, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper. The finite dependent enumeration contract is used in SparseCompletion.balanced_game_witness, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_uniform_score_mean, SparseCompletion.partition_game_witness, SparseCompletion.sum_bin_partition, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper. Pure scalar and ordinal-arithmetic helpers are excluded from finite-enumeration coverage.

The finSigmaFinEquiv offset/bijection and Finset.sigma membership/sum bridges are proved contracts from the pinned upstream theorems, not claimed generic definitional unfolding. Equiv field laws and the reversal value bridges are recorded separately.

Nat.ceil and FloorSemiring provide the actual grid rounding in SparseCompletion.double_grid_support_upper, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp. The scalar double_grid_support_upper is excluded from finite-cardinality usage.

## Exact midpoint and finite-correction refinements

The following contracts additionally use finite enumeration, sums, cardinality and the canonical bin-label bijection: SparseCompletion.bin_error_finite_identity, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.balanced_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_odd_game_witness, SparseCompletion.odd_midpoint_error_identity, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_odd_support, SparseCompletion.binned_middle_positive, SparseCompletion.binned_middle_injective, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact, SparseCompletion.bin_middle_even_gap, SparseCompletion.bin_middle_odd_same, SparseCompletion.bin_quadratic_parity_identity, SparseCompletion.bin_odd_support. The ordinal middle-position and scalar rational identities do not add finite-set assumptions. Finset.image is used in exact odd-bin support: image membership supplies original labels, injectivity makes the h representatives distinct, and positive r makes every representative active. The support-upper theorem allows arbitrary real r; exact support requires r>0 and positive total size.

### Finset.image pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Image.lean

Whole-source SHA256: 215a8edc840c6972f66f6e1bcbec7db3b410efcde0ab91fbe9cd377b698a0593

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Image.lean#L277-L284

```lean

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl
```

### finite-image-membership pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Image.lean

Whole-source SHA256: 215a8edc840c6972f66f6e1bcbec7db3b410efcde0ab91fbe9cd377b698a0593

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Image.lean#L290-L294

```lean
variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp, grind =]
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map]
```

### finite-image-cardinality pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean

Whole-source SHA256: 901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L233-L234

```lean
theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by
  simpa only [card_map] using! (s.1.map f).toFinset_card_le
```

### finite-injective-image-cardinality pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean

Whole-source SHA256: 901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L257-L259

```lean
theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
  card_image_of_injOn fun _ _ _ _ h => H h
```

### Compiler Function.Injective

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean

Whole-source SHA256: 88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030

GitHub exact-commit blob d3526ccde628989d0d4658dbec3c3f334bcb7a7f matches the installed compiler source. Distinct inputs have distinct outputs; equivalently equality of function values implies equality of inputs.

```lean
/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
```

```lean
/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
@[expose]
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

```

Affected selected declarations: SparseCompletion.binned_middle_injective, SparseCompletion.binned_odd_game_witness, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact

## Additional moments and all residual masses

The finite-feature compression works on ((Fin k ⊕ Fin d) ⊕ Fin H), preserving both the actual anchor columns and arbitrary d extra linear measurements. The exact case uses H−1 hinge values and obtains its endpoint from the original score mean, with no extra game anchors. Existing finite sum, coproduct cardinality, convex recombination, interval-grid and reconstruction meanings apply. At r=0, nonnegative_mass_zero proves every residual coordinate vanishes; all observations and measurements are retained. The all-mass wrappers add literal finite-cardinality minima without assuming support positivity.

Additional affected contracts: SparseCompletion.nonnegative_mass_zero, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass.

## Score prefixes and fixed-tolerance conic systems

The exact score-prefix proof uses a nonempty finite maximum with membership and upper-bound contracts. Its definition is max′=sup′ of the identity; sup′ extracts the non-bottom finite supremum under a proof of nonemptiness. This data helper is retained as a proof contract, alongside literal Antitone and Finset.Nonempty predicate definitions. Zero threshold set and zero prefix are handled explicitly. The concrete rotatedLorentz predicate is fixed project code, with convention 2uv≥w² and u,v≥0; its value at v=1/2 is proved equivalent to the displayed quadratic. No imported cone-feasibility theorem is assumed.

Existing finite sums and compact separation support the completion characterizations. Existing Convex/StarConvex meanings support the direct mixture proofs, including arbitrary convex repertoires and literal families of linear inequalities. Scalar quadratic_rotated_cone has no finite-index premise. Additional contracts: SparseCompletion.threshold_is_score_prefix, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.prefix_cut_quadratic, SparseCompletion.quadratic_rotated_cone, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.finite_linear_mix, SparseCompletion.finite_mass_mix, SparseCompletion.prefix_quadratic_mix, SparseCompletion.prefix_system_convex, SparseCompletion.anchor_response_mix, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.linear_repertoire_convex.

### Antitone pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean

Whole-source SHA256: 9b75e423f4425994dec847788cbcf1a510fce43c1c69facba3f9cdef50ed37d6

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean#L67-L69

```lean
/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a
```

### Finset.Nonempty pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Empty.lean

Whole-source SHA256: bc77217d483f0e3f1e159e7911ea21cc69647dfcf795c232c218a0ec0bbea93a

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Empty.lean#L44-L50

```lean
/-- The property `s.Nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s

@[grind =]
theorem nonempty_def {s : Finset α} : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
```

### Finset.max' pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean

Whole-source SHA256: f9381a30f98377e15faa35c02d19d3fa0d6576c1709460ed699f4616e4d2539e

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L128-L136

```lean
/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
@[to_dual
/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `WithTop α`. -/]
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id
```

### finite-maximum-membership-bound pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean

Whole-source SHA256: f9381a30f98377e15faa35c02d19d3fa0d6576c1709460ed699f4616e4d2539e

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L140-L146

```lean
@[to_dual]
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

@[to_dual min'_le]
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
```

### nonempty-supremum-expansion pinned source

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean

Whole-source SHA256: d8d50163e1990cd27cf072b38fb3c78f60af5eba53d657ff2afec18d4e3d505b

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean#L525-L533

```lean
/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
@[to_dual
/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/]
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)
```


The normalized full-game wrapper SparseCompletion.normalized_known_anchor_conic_iff adds literal nonnegative block weights of mass1 and full-matrix skew/bounds under the explicit fixed K/D/p premodel conditions. It uses the same prefix-order, finite-sum and completion meanings as SparseCompletion.known_anchor_prefix_characterization.


## Interval and arbitrary-cover material meanings

### Finset.max'

Maximum element of a genuinely nonempty finite set in a linear order. Definition is sup' of identity; nonemptiness is required. Maximum membership and order contracts establish result semantics, including for a set formed by inserting0.

Used by: SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact.

### Finset.sup'

Supremum of the image of a genuinely nonempty finite set in a join semilattice. Uses WithBot.unbot after finite sup of lifted values, with a proof the result is not bottom. Finset.sup folds supremum with bottom; it is not arbitrary choice or a supremum assumed attained in a general infinite set.

Used by: SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact.

### Set.compl

Set membership complement: x belongs exactly when x is not in the original set. Complement subtype is distinct from the chosen set subtype. Its enumeration uses actual decidable membership, potentially noncomputable classical evidence, with no executable algorithm inferred.

Used by: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact.

### Fintype.equivFin

A noncomputable equivalence from a finite type to the ordinal of its cardinality. Chooses an equivalence from truncEquivFin using Classical.decEq and Trunc.out. It is a bijective relabeling; it does not impose score order or an algorithmic enumeration claim.

Used by: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact.

### Equiv.Set.sumCompl

The disjoint sum of a set subtype and its complement subtype is equivalent to the original type. Delegates to Equiv.sumCompl membership predicate. Forward map forgets subtype proofs; inverse branches on actual membership evidence. Both inverse laws are proved; every original label belongs exactly to one side.

Used by: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact.

### LinearOrder

A reflexive, transitive, antisymmetric and total ordering with decidable comparisons/equality and consistent min/max/comparison operations. Extends PartialOrder then Preorder then LE/LT. Preorder ties strict order to non-strict order and its asymmetric part; LinearOrder supplies totality, decidable instances, min/max definitions and comparison consistency. Finite maximum applies to its actual order, not an abstract numerical supremum assumption.

Used by: SparseCompletion.residual_loss_bound_ordered.

Compiler-owned Subtype is value plus predicate proof. Decidable at this exact compiler is a Bool decision plus reflection proof, with pointwise DecidablePred; it is not the older inductive representation. Classical finite enumeration is noncomputable. Insert0 supplies an actual element and no multiplicity, including the empty case; no unconditional cardinality increment is asserted. LinearOrder supplies totality, transitivity, antisymmetry and coherent strict comparisons. The maximum result is an attained finite supremum with genuine nonemptiness, never an unguarded empty maximum.

### Mathlib/Data/Finset/Max.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean

Whole-source SHA256: f9381a30f98377e15faa35c02d19d3fa0d6576c1709460ed699f4616e4d2539e

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L128-L136

```lean
/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' H` is its maximum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `WithBot α`. -/
@[to_dual
/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' H` is its minimum, as an
element of `α`, where `H` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `WithTop α`. -/]
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L140-L159

```lean
@[to_dual]
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

@[to_dual min'_le]
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

@[to_dual le_min']
theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _

@[to_dual]
theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[to_dual (attr := simp) le_min'_iff]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB

```

### Mathlib/Data/Finset/Lattice/Fold.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean

Whole-source SHA256: d8d50163e1990cd27cf072b38fb3c78f60af5eba53d657ff2afec18d4e3d505b

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean#L37-L45

```lean
section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
@[to_dual /-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/]
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊔ ·) ⊥ f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean#L517-L540

```lean

variable [SemilatticeSup α]

@[to_dual]
theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup ((↑) ∘ f : β → WithBot α) = ↑a :=
  (WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) (f b) rfl).imp fun _ ↦ And.left

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
@[to_dual
/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/]
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[to_dual (attr := simp)]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f) := by
  rw [sup', WithBot.coe_unbot]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Lattice/Fold.lean#L556-L569

```lean

@[to_dual (attr := simp) le_inf'_iff]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

@[to_dual le_inf'] alias ⟨_, sup'_le⟩ := sup'_le_iff

@[to_dual inf'_le]
theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

@[to_dual]
theorem isLUB_sup' {s : Finset α} (hs : s.Nonempty) : IsLUB s (sup' s hs id) :=
  ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩
```

### Mathlib/Order/WithBot.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/WithBot.lean

Whole-source SHA256: 04888dc906f21616c8fde024aa9ee2b6ac6431ae6fc071a74f7d686aad670c12

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/WithBot.lean#L208-L220

```lean
  simp [ne_bot_iff_exists]

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
@[to_dual
/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/]
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α | (x : α), _ => x

@[to_dual (attr := simp)]
lemma coe_unbot : ∀ (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

@[to_dual (attr := simp)]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl
```

### Mathlib/Data/Finset/Fold.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Fold.lean

Whole-source SHA256: 56f34b22259c3514109bfcc338371d6d0ce6e55e40d1b139f520c009cf8fb6d9

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Fold.lean#L31-L39

```lean

variable (op : β → β → β) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b
```

### Mathlib/Order/Lattice.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice.lean

Whole-source SHA256: 848c632cb02ed8fedafbe876e8a609e8855a7acb66e604505431d5a7b5dd3e48

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice.lean#L65-L77

```lean

/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class SemilatticeSup (α : Type u) extends PartialOrder α where
  /-- The binary supremum, used to derive `Max α` -/
  sup : α → α → α
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c
```

### Mathlib/Order/Defs/PartialOrder.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/PartialOrder.lean

Whole-source SHA256: 7af151b7c035aa9969999bd704a8820162900e4c0fdac65a97d64992bacaf0b8

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/PartialOrder.lean#L39-L50

```lean

/--
A preorder is a reflexive, transitive relation `≤`.
In a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.
You can override this definition to set a better def-eq.
-/
class Preorder (α : Type*) extends LE α, LT α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/PartialOrder.lean#L176-L179

```lean
/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type*) extends Preorder α where
  protected le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

```

### Mathlib/Order/Defs/LinearOrder.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/LinearOrder.lean

Whole-source SHA256: dd0130c240109d5bdd532d2b0bd72996941de49af84b4239fa0d1caae555106f

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/LinearOrder.lean#L59-L81

```lean
/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class LinearOrder (α : Type*) extends PartialOrder α, Min α, Max α, Ord α where
  /-- A linear order is total. -/
  protected le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  /-- The minimum function is equivalent to the one you get from `minOfLe`. -/
  protected min_def : ∀ a b, min a b = if a ≤ b then a else b := by intros; rfl
  /-- The minimum function is equivalent to the one you get from `maxOfLe`. -/
  protected max_def : ∀ a b, max a b = if a ≤ b then b else a := by intros; rfl
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

attribute [to_dual existing] LinearOrder.toMax
```

### Mathlib/Data/Set/Defs.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

Whole-source SHA256: 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L246-L250

```lean
/-- The complement of a set `s` is the set of elements not contained in `s`.

Note that you should **not** use this definition directly, but instead write `sᶜ`. -/
protected def compl (s : Set α) : Set α := {a | a ∉ s}

```

### Mathlib/Data/Set/CoeSort.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/CoeSort.lean

Whole-source SHA256: a6321ae732b4e66276846dbe00faf4bec0ef17eed151ca268d8d29845d47c3fc

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/CoeSort.lean#L30-L40

```lean
/-- Given the set `s`, `Elem s` is the `Type` of element of `s`.

It is currently an abbreviation so that instance coming from `Subtype` are available.
If you're interested in making it a `def`, as it probably should be,
you'll then need to create additional instances (and possibly prove lemmas about them).
See e.g. `Mathlib/Data/Set/Order.lean`.
-/
@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

/-- Coercion from a set to the corresponding subtype. -/
instance : CoeSort (Set α) (Type u) := ⟨Elem⟩
```

### Mathlib/Data/Fintype/EquivFin.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/EquivFin.lean

Whole-source SHA256: 891fdb687fc067b1511701992301e28de0d4fd6ab53d74a96f51be39d5aa8f92

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/EquivFin.lean#L51-L72

```lean

/-- There is (computably) an equivalence between `α` and `Fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `Trunc` to
preserve computability.

See `Fintype.equivFin` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.

See `Fintype.truncFinBijection` for a version without `[DecidableEq α]`.
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/EquivFin.lean#L73-L82

```lean

/-- There is (noncomputably) an equivalence between `α` and `Fin (card α)`.

See `Fintype.truncEquivFin` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out
```

### Mathlib/Data/Fintype/Defs.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean

Whole-source SHA256: e69e8e7a3605d293a7ef6c4a7aaefde3191da4f33b43b7be09963eec2e44965c

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean#L267-L273

```lean
/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
@[instance_reducible]
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩
```

### Mathlib/Data/Fintype/Sets.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sets.lean

Whole-source SHA256: 87b401f8e6bf02de9250adba00dcb1de4157d55e286f6e627d01639fe2b2ef9a

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sets.lean#L245-L267

```lean
instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp⟩, by simpa using em⟩

@[simp]
theorem Fintype.univ_Prop [DecidableEq Prop] : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp; rfl

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
@[instance_reducible]
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s
```

### Mathlib/Logic/Equiv/Set.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Set.lean

Whole-source SHA256: 90eaaedccc63f81347c8918ffa50665fd01c8bca02585c104b3d3f484db673a7

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Set.lean#L304-L328

```lean

/-- If `s : Set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`.

See also `Equiv.sumCompl`. -/
protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : s ⊕ (sᶜ : Set α) ≃ α :=
  Equiv.sumCompl (· ∈ s)

@[simp]
theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
    Equiv.Set.sumCompl s (Sum.inl x) = x :=
  rfl

@[simp]
theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
    Equiv.Set.sumCompl s (Sum.inr x) = x :=
  rfl

theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_pos hx

theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
  sumCompl_symm_apply_of_neg hx

```

### Mathlib/Logic/Equiv/Sum.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Sum.lean

Whole-source SHA256: df604983467488d4bc91a59822530bc04cad0ec59a0ca7831e08c5932d9cb791

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Sum.lean#L254-L301

```lean

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtypeOrEquiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `IsCompl p q`. See also `Equiv.Set.sumCompl` for a version on sets. -/
def sumCompl {α : Type*} (p : α → Prop) [DecidablePred p] :
    { a // p a } ⊕ { a // ¬p a } ≃ α where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun a := if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩
  left_inv := by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp
    · rw [dite_eq_left]
    · rw [dite_eq_right]
  right_inv a := by
    dsimp
    split_ifs <;> rfl

@[simp]
theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
    sumCompl p (Sum.inl x) = x :=
  rfl

@[simp]
theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
    sumCompl p (Sum.inr x) = x :=
  rfl

@[simp]
theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
  dite_eq_left h

@[simp]
theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
  dite_eq_right h

@[simp]
theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
    (sumCompl p).symm x = Sum.inl x :=
  sumCompl_symm_apply_of_pos x.2

@[simp]
theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
    (sumCompl p).symm x = Sum.inr x :=
  sumCompl_symm_apply_of_neg x.2
```

### Mathlib/Data/Finset/Insert.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Insert.lean

Whole-source SHA256: 9b5eb2047d48845dfff399259ddcf3b27fc760fdac9f704e4e641f771554ad35

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Insert.lean#L342-L369

```lean

section Insert

variable [DecidableEq α] {s t : Finset α} {a b : α} {f : α → β}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl

@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl

theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self]; rfl

theorem insert_val_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_notMem h]

@[simp, grind =]
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert

theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Insert.lean#L423-L426

```lean

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩
```

### Mathlib/Data/Multiset/FinsetOps.lean retained expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/FinsetOps.lean

Whole-source SHA256: 6f0955956933081804aa30ca9d96becdf112d46c1bf901e93b62792cdc4c1124

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/FinsetOps.lean#L31-L42

```lean
/-! ### finset insert -/


/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `Finset`. -/
def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]
theorem coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α) :=
  rfl
```

### Exact compiler expansions

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean

Whole-source SHA256: cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39; Git blob f87ee970af5149d74434f09a89aedff1a8fdb2d2.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L693-L721

```lean
theorem Or.neg_resolve_right (h : Or a (Not b)) (nb : b) : a := h.elim id (absurd nb)
/--
All the elements of a type that satisfy a predicate.

`Subtype p`, usually written `{ x : α // p x }` or `{ x // p x }`, contains all elements `x : α` for
which `p x` is true. Its constructor is a pair of the value and the proof that it satisfies the
predicate. In run-time code, `{ x : α // p x }` is represented identically to `α`.

There is a coercion from `{ x : α // p x }` to `α`, so elements of a subtype may be used where the
underlying type is expected.

Examples:
 * `{ n : Nat // n % 2 = 0 }` is the type of even numbers.
 * `{ xs : Array String // xs.size = 5 }` is the type of arrays with five `String`s.
 * Given `xs : List α`, `List { x : α // x ∈ xs }` is the type of lists in which all elements are
   contained in `xs`.
-/
@[pp_using_anonymous_constructor]
structure Subtype {α : Sort u} (p : α → Prop) where
  /--
  The value in the underlying type that satisfies the predicate.
  -/
  val : α
  /--
  The proof that `val` satisfies the predicate `p`.
  -/
  property : p val

grind_pattern Subtype.property => self.val
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1120-L1128

```lean
/--
Equivalence between a boolean and a proposition.

`b.Reflects p` is propositionally equivalent to `b = true ↔ p` but has the definitional equalities
`true.Reflects p ↔ p` and `false.Reflects p ↔ ¬p`.
-/
abbrev Bool.Reflects : Bool → Prop → Prop
  | false, p => Not p
  | true, p => p
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1130-L1182

```lean
/--
A `Bool` (that is, `decide p`) paired with a proof of `p` if `decide p` is `true` or a proof of `¬p`
if `decide p` is `false`. The easiest way to extract these proofs is to use `of_decide_eq_true` or
`of_decide_eq_false`.

`Decidable` instances are primarily used via `if`-expressions and the tactic `decide`. In
conditional expressions, the `Decidable` instance for the proposition is used to select a branch. At
run time, this case distinction code is identical to that which would be generated for a
`Bool`-based conditional. In proofs, the tactic `decide` synthesizes an instance of `Decidable p`,
attempts to reduce `decide p` to `true`, and then succeeds with the proof `of_decide_eq_true rfl`
if it can.

Because `Decidable` carries data, when writing `@[simp]` lemmas which include a `Decidable` instance
on the LHS, it is best to use `{_ : Decidable p}` rather than `[Decidable p]` so that non-canonical
instances can be found via unification rather than instance synthesis.
-/
class Decidable (p : Prop) where
  /--
  Introduces `Decidable p` using a boolean `decide` and a proof of `¬p` if `decide` is `false`
  or `p` if `decide` is `true`.
  -/
  intro ::
  /--
  Converts a decidable proposition into a `Bool`.

  If `p : Prop` is decidable, then `decide p : Bool` is the Boolean value
  that is `true` if `p` is true and `false` if `p` is false.
  -/
  decide : Bool
  /--
  `decide p` reflects `p`, i.e. `decide p` is equivalent to `p`. Reduces to a proof of `p` or `¬p`
  depending on the value of `decide p`.
  -/
  reflects_decide (p) : decide.Reflects p

attribute [implicit_reducible] Decidable.decide

/-- Proves that `p` is decidable by supplying a proof of `¬p` -/
@[match_pattern] abbrev Decidable.isFalse (h : Not p) : Decidable p := ⟨false, h⟩

/-- Proves that `p` is decidable by supplying a proof of `p` -/
@[match_pattern] abbrev Decidable.isTrue (h : p) : Decidable p := ⟨true, h⟩

/--
The default eliminator for `Decidable`, using `isFalse` and `isTrue`.
-/
@[cases_eliminator, induction_eliminator, elab_as_elim]
abbrev Decidable.falseTrueCases {p : Prop} {motive : Decidable p → Sort u}
    (isFalse : ∀ h, motive (isFalse h)) (isTrue : ∀ h, motive (isTrue h))
    (t : Decidable p) : motive t :=
  t.casesOn fun x => x.casesOn isFalse isTrue

export Decidable (isTrue isFalse decide)
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1184-L1190

```lean
/--
A decidable predicate.

A predicate is decidable if the corresponding proposition is `Decidable` for each possible argument.
-/
abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1398-L1410

```lean
instance instOfNatNat (n : Nat) : OfNat Nat n where
  ofNat := n

/-- `LE α` is the typeclass which supports the notation `x ≤ y` where `x y : α`.-/
class LE (α : Type u) where
  /-- The less-equal relation: `x ≤ y` -/
  le : α → α → Prop

/-- `LT α` is the typeclass which supports the notation `x < y` where `x y : α`.-/
class LT (α : Type u) where
  /-- The less-than relation: `x < y` -/
  lt : α → α → Prop

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1415-L1445

```lean

/-- Abbreviation for `DecidableRel (· < · : α → α → Prop)`. -/
abbrev DecidableLT (α : Type u) [LT α] := DecidableRel (LT.lt : α → α → Prop)
/-- Abbreviation for `DecidableRel (· ≤ · : α → α → Prop)`. -/
abbrev DecidableLE (α : Type u) [LE α] := DecidableRel (LE.le : α → α → Prop)

/--
An overloaded operation to find the greater of two values of type `α`.
-/
class Max (α : Type u) where
  /-- Returns the greater of its two arguments. -/
  max : α → α → α

export Max (max)

/--
Constructs a `Max` instance from a decidable `≤` operation.
-/
-- Marked inline so that `min x y + max x y` can be optimized to a single branch.
@[inline, instance_reducible]
def maxOfLe [LE α] [DecidableRel (@LE.le α _)] : Max α where
  max x y := ite (LE.le x y) y x

/--
An overloaded operation to find the lesser of two values of type `α`.
-/
class Min (α : Type u) where
  /-- Returns the lesser of its two arguments. -/
  min : α → α → α

export Min (min)
```

Both semantic entrypoints compile finite maximum/supremum contracts, insert-zero membership/nonemptiness/literal data, complement membership, subtype property/enumeration, finite-type equivalence and partition maps/inverse, literal DecidablePred and actual reflection, and the order contract. Their successful compilation belongs to the exact-source receipt.

Additional selected coverage for Finset.max': SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_bound_le, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_maximum.

Additional selected coverage for Finset.sup': SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_bound_le, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_maximum.

Additional selected coverage for Set.compl: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

Additional selected coverage for Fintype.equivFin: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

Additional selected coverage for Equiv.Set.sumCompl: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

Additional selected coverage for LinearOrder: SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered.

## Existing meanings in the interval/cover contracts

The following usage expansion records actual new finite sums, enumeration, image/maxima, cardinality, relabeling, moment compression and completion dependencies. Scalar recovery and projection lemmas do not acquire unrelated geometric assumptions. Legacy coverage remains unchanged.

Fintype: SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_recovered_score_moment, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.perspective_cuts_iff, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered, SparseCompletion.residual_projection_response_bound, SparseCompletion.score_lower_from_intervals.

Finset: SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_recovered_score_moment, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.perspective_cuts_iff, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered, SparseCompletion.residual_projection_response_bound, SparseCompletion.score_lower_from_intervals.

Finset.prod: SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_recovered_score_moment, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.perspective_cuts_iff, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.residual_projection_response_bound, SparseCompletion.score_lower_from_intervals.

Set.Icc: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Nat.ceil: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

FloorSemiring: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

NNReal.sqrt: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Real.sqrt: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Real.toNNReal: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Convex: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

StarConvex: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

convexHull: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

AffineIndependent: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Finset.weightedVSub: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Finset.weightedVSubOfPoint: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

vectorSpan: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Submodule.span: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Module.finrank: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Finset.card: SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.relabel_support_card.

Fintype.card: SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

IsCompact: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

IsClosed: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Continuous: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

LinearMap: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

ContinuousLinearMap: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Set.image: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness.

Equiv: SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.relabel_intervals, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_skew, SparseCompletion.relabel_support_card, SparseCompletion.split_skew_matrix, SparseCompletion.split_weights.

Finset.image: SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered.

Finset.Nonempty: SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty.


Compact-convex completion coverage for Convex: SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_interval_perspective_iff.

Compact-convex completion coverage for StarConvex: SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_interval_perspective_iff.

Set.Icc also appears as the coordinatewise bounded matrix cube in compact completion reconstruction for SparseCompletion.interval_perspective_completion_iff, SparseCompletion.normalized_interval_perspective_iff. This uses the same literal closed order-interval predicate, with pointwise matrix order.
