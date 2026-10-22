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


## Joint interval geometry, actual minima, and cloned anchors

### Mathlib/Algebra/Notation/Prod.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Prod.lean

Whole-source SHA256: 04b328557e18a8f75955a89484cda74bfeb9bb685e62d0b59ab70f01477dfd4a

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Prod.lean#L61-L82

```lean
section Mul

variable {M N : Type*} [Mul M] [Mul N]

@[to_additive]
instance instMul : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl

@[to_additive (attr := simp)]
theorem snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl

@[to_additive (attr := simp)]
theorem mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

@[to_additive (attr := simp)]
theorem swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl

@[to_additive]
theorem mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Prod.lean#L132-L152

```lean
section Pow

variable {E α β : Type*} [Pow α E] [Pow β E]

@[to_additive (attr := to_additive) instSMul]
instance instPow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_fst]
lemma pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_snd]
lemma pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

@[to_additive (attr := to_additive, simp) (reorder := a b c) smul_mk]
lemma pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

@[to_additive (attr := to_additive) (reorder := p c) smul_def]
lemma pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

@[to_additive (attr := to_additive, simp) (reorder := p c) smul_swap]
lemma pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c := rfl
```

### Mathlib/Algebra/Notation/Pi/Defs.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Pi/Defs.lean

Whole-source SHA256: 79c1a26611ae1d19d22b47b0b109eb02ff5502545b55e7ad96b2a9164622a89c

```lean
/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Pi/Defs.lean#L63-L73

```lean
section Mul
variable [∀ i, Mul (M i)]

@[to_additive]
instance instMul : Mul (∀ i, M i) where mul f g i := f i * g i

@[to_additive (attr := simp)]
lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl

@[to_additive (attr := push ←)]
lemma mul_def (f g : ∀ i, M i) : f * g = fun i ↦ f i * g i := rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Notation/Pi/Defs.lean#L128-L139

```lean
section Pow

variable [∀ i, Pow (M i) α]

@[to_additive (attr := to_additive) instSMul]
instance instPow : Pow (∀ i, M i) α where pow f a i := f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
lemma pow_apply (f : ∀ i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

@[to_additive (attr := push ←, to_additive) (reorder := 5 6) smul_def]
lemma pow_def (f : ∀ i, M i) (a : α) : f ^ a = fun i ↦ f i ^ a := rfl
```

### Mathlib/Algebra/Group/Action/Defs.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Action/Defs.lean

Whole-source SHA256: ffecdd8214bad55eab6c631352ec37254a3459a674362fc43681ebfef8ede9b9

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Action/Defs.lean#L74-L75

```lean
@[to_additive (attr := simp)]
lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl
```

### Compiler-owned product and finite-sum meanings

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean

Whole-source SHA256: cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39; Git blob f87ee970af5149d74434f09a89aedff1a8fdb2d2.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L602-L620

```lean

/--
The product type, usually written `α × β`. Product types are also called pair or tuple types.
Elements of this type are pairs in which the first element is an `α` and the second element is a
`β`.

Products nest to the right, so `(x, y, z) : α × β × γ` is equivalent to `(x, (y, z)) : α × (β × γ)`.
-/
structure Prod (α : Type u) (β : Type v) where
  /--
  Constructs a pair. This is usually written `(x, y)` instead of `Prod.mk x y`.
  -/
  mk ::
  /-- The first element of a pair. -/
  fst : α
  /-- The second element of a pair. -/
  snd : β

attribute [unbox] Prod
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1635-L1651

```lean
  one : α

/-- The homogeneous version of `HAdd`: `a + b : α` where `a b : α`. -/
class Add (α : Type u) where
  /-- `a + b` computes the sum of `a` and `b`. See `HAdd`. -/
  add : α → α → α

/-- The homogeneous version of `HSub`: `a - b : α` where `a b : α`. -/
class Sub (α : Type u) where
  /-- `a - b` computes the difference of `a` and `b`. See `HSub`. -/
  sub : α → α → α

/-- The homogeneous version of `HMul`: `a * b : α` where `a b : α`. -/
class Mul (α : Type u) where
  /-- `a * b` computes the product of `a` and `b`. See `HMul`. -/
  mul : α → α → α

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1721-L1725

```lean
/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class SMul (M : Type u) (α : Type v) where
  /-- `m • a : α` denotes the product of `m : M` and `a : α`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  smul : M → α → α
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L1818-L1824

```lean
@[default_instance]
instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

instance (priority := 910) {α : Type u} [Mul α] : SMul α α where
  smul x y := Mul.mul x y

```

### Mathlib/Order/SetNotation.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean

Whole-source SHA256: 302c614100cbc978e2af66d21d5eb0e09eb39402e9ae52a166e6faaa36d3dc14

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean#L43-L56

```lean
/-- Class for the `sSup` operator -/
class SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α → α

/-- Class for the `sInf` operator -/
@[to_dual existing]
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α

export SupSet (sSup)

export InfSet (sInf)
```

### Mathlib/Order/ConditionallyCompleteLattice/Defs.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/ConditionallyCompleteLattice/Defs.lean

Whole-source SHA256: 69a260fe2f698bec70175570cdcc411e231b36cc62845cc5ad061da43e4fc7b0

```lean
/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/ConditionallyCompleteLattice/Defs.lean#L37-L82

```lean
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLattice (α : Type*) extends Lattice α, SupSet α, InfSet α where
  /-- Every nonempty subset which is bounded above has a least upper bound. -/
  isLUB_csSup : ∀ s : Set α, s.Nonempty → BddAbove s → IsLUB s (sSup s)
  /-- Every nonempty subset which is bounded below has a greatest lower bound. -/
  isGLB_csInf : ∀ s : Set α, s.Nonempty → BddBelow s → IsGLB s (sInf s)

attribute [to_dual self (reorder := 3 4, 5 6)] ConditionallyCompleteLattice.mk
attribute [to_dual existing] ConditionallyCompleteLattice.toSupSet
attribute [to_dual existing] ConditionallyCompleteLattice.isLUB_csSup

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrder (α : Type*)
    extends ConditionallyCompleteLattice α, Ord α where
  /-- A `ConditionallyCompleteLinearOrder` is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  /-- If a set is not bounded above, its supremum is by convention `sSup ∅`. -/
  csSup_of_not_bddAbove : ∀ s, ¬BddAbove s → sSup s = sSup (∅ : Set α)
  /-- If a set is not bounded below, its infimum is by convention `sInf ∅`. -/
  csInf_of_not_bddBelow : ∀ s, ¬BddBelow s → sInf s = sInf (∅ : Set α)
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl
```

### Mathlib/Order/ConditionallyCompleteLattice/Basic.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean

Whole-source SHA256: f3ccc930eeef8bd3cdd245cd88e9941a3b226f0baf0e83029b7c86897fa2a224

```lean
/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean#L188-L202

```lean
section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

@[to_dual]
theorem isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s := by bddDefault) : IsLUB s (sSup s) :=
  ConditionallyCompleteLattice.isLUB_csSup _ hn hb

@[to_dual csInf_le]
theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]
theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂
```

### Mathlib/Algebra/Order/Archimedean/Real/Basic.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean

Whole-source SHA256: 1c03e3aecbfa3739e79ae8ebfd33b6100781d4c90e6475677cdcff4487e972d1

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L106-L142

```lean
/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : ∃ x, IsGLB s x := by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

open scoped Classical in
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
theorem sSup_def (s : Set ℝ) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl

protected theorem isLUB_sSup (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dite_eq_left (And.intro h₁ h₂)]
  apply Classical.choose_spec

noncomputable instance : InfSet ℝ :=
  ⟨fun s => -sSup (-s)⟩

theorem sInf_def (s : Set ℝ) : sInf s = -sSup (-s) := rfl

protected theorem isGLB_sInf (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg

noncomputable instance : ConditionallyCompleteLinearOrder ℝ where
  __ := Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]
```

### Mathlib/Order/Bounds/Defs.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Bounds/Defs.lean

Whole-source SHA256: e5a38e3cf5b12a87a53bbd64d4d458bacb2f707aa75e1b3dca1c33014aa23c2d

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Bounds/Defs.lean#L30-L52

```lean
variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
@[to_dual /-- The set of lower bounds of a set. -/]
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- A set is bounded above if there exists an upper bound. -/
@[to_dual /-- A set is bounded below if there exists a lower bound. -/]
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
@[to_dual
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/]
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)
```

### Mathlib/Topology/Order/Compact.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Compact.lean

Whole-source SHA256: 7c02670f2e88f16acd11d69ddd6afb8d8118adca50279e1abb2a3c7761feb044

```lean
/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Compact.lean#L142-L156

```lean
section LinearOrder

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β]

theorem IsCompact.exists_isLeast [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x, IsLeast s x := by
  have : Nonempty s := ne_s.to_subtype
  suffices (s ∩ ⋂ x ∈ s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic ↑x) (fun x => isClosed_Iic) H
      (Monotone.directed_ge fun _ _ h => Iic_subset_Iic.mpr h) with ⟨x, hx⟩
  exact disjoint_left.mp hx x.2 le_rfl
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Compact.lean#L313-L319

```lean
/-- A compact set is bounded below -/
theorem IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddBelow s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Compact.lean#L375-L383

```lean
section InfSup

variable {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β]

theorem IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sInf s ∈ s :=
  let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem
```

### Mathlib/Data/Set/Operations.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

Whole-source SHA256: 60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L219-L229

```lean
section Prod

/-- The Cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
@[wikidata Q173740]
def prod (s : Set α) (t : Set β) : Set (α × β) := {p | p.1 ∈ s ∧ p.2 ∈ t}

@[default_instance]
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod

theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t := rfl
```

### Mathlib/Data/Set/Defs.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

Whole-source SHA256: 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L263-L268

```lean
universe v in
/-- The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that
`f a = b` for some `a ∈ s`. -/
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

instance : Functor Set where map := @Set.image
```

### Mathlib/Topology/Constructions/SumProd.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean

Whole-source SHA256: 35d6365bebe8c5d331fe01289e857ccc81e6f6392b1f01835d834a35a6931666

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean#L47-L55

```lean
variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂
```

### Mathlib/Topology/Defs/Induced.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

Whole-source SHA256: ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L59-L74

```lean
/-- Given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous. -/
@[instance_reducible]
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
```

### Mathlib/Topology/Order.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

Whole-source SHA256: 2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L180-L195

```lean
  a topology to its collection of open subsets, and whose upper part sends a collection of subsets
  of `α` to the topology they generate. -/
def gciGenerateFrom (α : Type*) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | IsOpen[t] s })
      (generateFrom ∘ OrderDual.ofDual) where
  gc := gc_generateFrom α
  u_l_le _ s hs := TopologicalSpace.GenerateOpen.basic s hs
  choice g hg := TopologicalSpace.mkOfClosure g
    (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq _ _ := mkOfClosure_sets

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) := (gciGenerateFrom α).liftCompleteLattice
```

### Mathlib/Topology/Compactness/Compact.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean

Whole-source SHA256: 3fc7ffe7db4db0a2de07d6fdf0e65da486b3dced1f3bac4d58ab869a92f4ac64

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L110-L126

```lean
@[compactness .]
theorem IsCompact.image_of_continuousOn {f : X → Y} (hs : IsCompact s) (hf : ContinuousOn f s) :
    IsCompact (f '' s) := by
  intro l lne ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L1071-L1082

```lean
@[compactness .]
theorem IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×ˢ t) := by
  rw [isCompact_iff_ultrafilter_le_nhds'] at hs ht ⊢
  intro f hfs
  obtain ⟨x : X, sx : x ∈ s, hx : map Prod.fst f.1 ≤ 𝓝 x⟩ :=
    hs (f.map Prod.fst) (mem_map.2 <| mem_of_superset hfs fun x => And.left)
  obtain ⟨y : Y, ty : y ∈ t, hy : map Prod.snd f.1 ≤ 𝓝 y⟩ :=
    ht (f.map Prod.snd) (mem_map.2 <| mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at hx hy
  refine ⟨⟨x, y⟩, ⟨sx, ty⟩, ?_⟩
  rw [nhds_prod_eq]; exact le_inf hx hy
```

### Mathlib/Topology/Order/OrderClosed.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/OrderClosed.lean

Whole-source SHA256: e311dbc7fca744dc0f0d4a10e3c838eb4996c2fa8b63e833077c40f763f05444

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/OrderClosed.lean#L71-L75

```lean
/-- If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `Iic a` is
closed for all `a : α`. -/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/OrderClosed.lean#L446-L453

```lean
@[to_dual self (reorder := f g, hf hg)]
theorem isClosed_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b ≤ g b } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]
instance : ClosedIicTopology α where
  isClosed_Iic _ := isClosed_le continuous_id continuous_const
```

### Mathlib/Topology/Order/Basic.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Basic.lean

Whole-source SHA256: 70041d69776fc6d4a8c15c7c9da1b6c01b11fe8d3194ca7aebccebec539c7db2

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Basic.lean#L400-L418

```lean
section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology
variable [OrderTopology α]

@[to_dual none]
theorem order_separated {a₁ a₂ : α} (h : a₁ < a₂) :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ ∀ b₁ ∈ u, ∀ b₂ ∈ v, b₁ < b₂ :=
  let ⟨x, hx, y, hy, h⟩ := h.exists_disjoint_Iio_Ioi
  ⟨Iio x, Ioi y, isOpen_gt' _, isOpen_lt' _, hx, hy, h⟩

-- see Note [lower instance priority]
instance (priority := 100) OrderTopology.to_orderClosedTopology : OrderClosedTopology α where
  isClosed_le' := isOpen_compl_iff.1 <| isOpen_prod_iff.mpr fun a₁ a₂ (h : ¬a₁ ≤ a₂) =>
    have h : a₂ < a₁ := lt_of_not_ge h
    let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h
    ⟨v, u, hv, hu, ha₂, ha₁, fun ⟨b₁, b₂⟩ ⟨h₁, h₂⟩ => not_le_of_gt <| h b₂ h₂ b₁ h₁⟩
```

### Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean

Whole-source SHA256: 6a0cf742b00efa9cbd7f386a61c33a84710797bc1fb1cb82d8d92e1951b4df6a

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean#L17-L25

```lean

open Filter Metric Set
open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]
```

### Compiler-owned product and finite-sum meanings

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean

Whole-source SHA256: cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39; Git blob f87ee970af5149d74434f09a89aedff1a8fdb2d2.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L35-L44

```lean
set_option bootstrap.inductiveCheckResultingUniverse false in
/--
The canonical universe-polymorphic type with just one element.

It should be used in contexts that require a type to be universe polymorphic, thus disallowing
`Unit`.
-/
inductive PUnit : Sort u where
  /-- The only element of the universe-polymorphic unit type. -/
  | unit : PUnit
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L214-L231

```lean
/--
The canonical type with one element. This element is written `()`.

`Unit` has a number of uses:
 * It can be used to model control flow that returns from a function call without providing other
   information.
 * Monadic actions that return `Unit` have side effects without computing values.
 * In polymorphic types, it can be used to indicate that no data is to be stored in a particular
   field.
-/
abbrev Unit : Type := PUnit

/--
The only element of the unit type.

It can be written as an empty tuple: `()`.
-/
@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit
```

### Compiler-owned product and finite-sum meanings

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Core.lean

Whole-source SHA256: 264a0b48fedc91fadf55fc5caac8d91003e3908a6e5e42736e2ac8bf1f7cdf99; Git blob 23e784c3806badcabd1e8f19c50946d66bc3c87a.

```lean
/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Core.lean#L202-L218

```lean

/--
The disjoint union of types `α` and `β`, ordinarily written `α ⊕ β`.

An element of `α ⊕ β` is either an `a : α` wrapped in `Sum.inl` or a `b : β` wrapped in `Sum.inr`.
`α ⊕ β` is not equivalent to the set-theoretic union of `α` and `β` because its values include an
indication of which of the two types was chosen. The union of a singleton set with itself contains
one element, while `Unit ⊕ Unit` contains distinct values `inl ()` and `inr ()`.
-/
@[suggest_for Either]
inductive Sum (α : Type u) (β : Type v) where
  /-- Left injection into the sum type `α ⊕ β`. -/
  | inl (val : α) : Sum α β
  /-- Right injection into the sum type `α ⊕ β`. -/
  | inr (val : β) : Sum α β

@[inherit_doc] infixr:30 " ⊕ " => Sum
```

### Compiler-owned product and finite-sum meanings

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Sum/Basic.lean

Whole-source SHA256: c58e4b1ef684fdb842d6ae50fff0501fadd58dc8121773b00630e9e25ee1ac51; Git blob 7179f792183250f7947a7718abd04fcb7b725c98.

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Sum/Basic.lean#L99-L111

```lean
/--
Case analysis for sums that applies the appropriate function `f` or `g` after checking which
constructor is present.
-/
@[expose] protected def elim {α β γ} (f : α → γ) (g : β → γ) : α ⊕ β → γ :=
  fun x => Sum.casesOn x f g

@[simp, grind =] theorem elim_inl (f : α → γ) (g : β → γ) (x : α) :
    Sum.elim f g (inl x) = f x := rfl

@[simp, grind =] theorem elim_inr (f : α → γ) (g : β → γ) (x : β) :
    Sum.elim f g (inr x) = g x := rfl

```

### Mathlib/Data/Fintype/Sum.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sum.lean

Whole-source SHA256: ade79778a014dce4b3b7c3f473295010528795d9188c15f5a9c3a0c31106cf18

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sum.lean#L25-L28

```lean
open Finset

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (α ⊕ β) where
  elems := univ.disjSum univ
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sum.lean#L62-L65

```lean
@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _
```

### Mathlib/Data/Fintype/Basic.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Basic.lean

Whole-source SHA256: 3c4b1e41181451d1965b55e9a8c558d4f2a08b46dbdd47489950027629a395c0

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Basic.lean#L135-L139

```lean
instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl
```

### Mathlib/Data/Fintype/OfMap.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/OfMap.lean

Whole-source SHA256: 1fcb10b0b6b6789534a5bd2b3f93312cce927035fec0bc4eebe705ccf8662af6

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/OfMap.lean#L77-L85

```lean
/-- Any subsingleton type with a witness is a fintype (with one term). -/
@[instance_reducible]
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

-- In principle, this could be a `simp` theorem but it applies to any occurrence of `univ` and
-- required unification of the (possibly very complex) `Fintype` instances.
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl
```

### Mathlib/Data/Fintype/Card.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean

Whole-source SHA256: a77eb573a459ee525cfb4ac753dd05968ef2cc831d7549dc4e9036c7a90a1f00

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean#L174-L175

```lean
theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl
```

### Mathlib/Data/Fintype/BigOperators.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean

Whole-source SHA256: b9a6354ebff5fcd22fb1ddb7992682a404ec44c8ee42d519177f17d1d5a239e9

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean#L260-L268

```lean
@[to_additive]
theorem Fintype.prod_sumElim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disjSum _ _ _

@[to_additive (attr := simp)]
theorem Fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disjSum _ _ _
```

### Mathlib/Data/Finset/Sum.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sum.lean

Whole-source SHA256: 0f383b603d87d7cdad80e1e86de933f4158edcaa85883521fa8a8fb369673b5b

```lean
/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Sum.lean#L28-L35

```lean

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

/-- Disjoint sum of finsets. -/
def disjSum : Finset (α ⊕ β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩
```

### Mathlib/Data/Multiset/Sum.lean exact expansion

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Sum.lean

Whole-source SHA256: 46ad986a41048710426d3296a8284bc983e91e0a000d6a497db675e512528c15

```lean
/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Sum.lean#L24-L32

```lean
open Sum

namespace Multiset

variable {α β γ : Type*} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
def disjSum : Multiset (α ⊕ β) :=
  s.map inl + t.map inr
```

### InfSet material account

A typeclass supplying a total set-infimum operator, with no minimum law asserted by this field alone. The actual Real instance is -sSup(-s). Conditional completeness proves greatest-lower-bound semantics on nonempty bounded-below inputs; compactness and nonemptiness are proved for the actual compatible matrix/strategy image. Invalid or empty inputs are not claimed to attain a minimum.

Used by: SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_support_value_ordered_stability.

### ConditionallyCompleteLattice material account

Every nonempty bounded-below set has a greatest lower bound; dually for suprema. Real uses its proved isGLB_sInf and isLUB_sSup. BddBelow and IsGLB are generated duals of retained bounds definitions. The actual value image is compact and nonempty before sInf membership/lower-bound theorems are applied.

Used by: SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_support_value_ordered_stability.

### ConditionallyCompleteLinearOrder material account

Conditional completeness together with a total ordered structure and coherent decidable comparisons. On reals this is the retained canonical instance. Outside bounded sets the operation is total by convention; all claimed optimistic minima use actual compact nonempty sets.

Used by: SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_support_value_ordered_stability.

### Set.prod material account

Cartesian product membership is conjunction of memberships of the two projections. The topology is the ordinary product topology given by the infimum of projection-induced topologies (topologies use reverse order). Compact matrix and strategy sets therefore have compact product, and continuous exploitability gives a compact value image.

Used by: SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.exploitability_continuous.

Product tuples are right associated: (q,V,K) means q,(V,K); projections .1,.2.1,.2.2 have literal semantic bridges. Product and function addition/scalar multiplication are componentwise generated instances, not tensor products. Unit is the genuine one-element type, and Sum is a disjoint union; clone aggregation uses actual singleton/sum enumeration and cardinality. The real infimum is not an assumed target minimum: attainment follows from proved compactness, continuity and nonempty admissibility.


## Selected interval, stability, gap and joint-support dependencies

These additions combine exact reviewed dependency groups with source-reference closure. Imported operation expansions propagate from natural ceiling to FloorSemiring and from real square root to NNReal.sqrt/Real.toNNReal. They supplement immutable earlier usage lists; actual semantic completeness requires independent review.

AffineIndependent: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

ConditionallyCompleteLattice: SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

ConditionallyCompleteLinearOrder: SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

Continuous: SparseCompletion.exact_completion_gap_point, SparseCompletion.exploitability_continuous, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

ContinuousLinearMap: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

Convex: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.perspective_cut_system_convex, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.variable_core_interval_completion_iff.

Finset: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.exact_completion_gap_point, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_perturbation, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.perspective_quadratic_mix, SparseCompletion.positive_score_call_identity, SparseCompletion.positive_score_threshold, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.response_le_exploitability, SparseCompletion.shifted_call_antitone, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff.

Finset.Nonempty: SparseCompletion.positive_score_threshold.

Finset.card: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.clone_support_card, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff.

Finset.orderEmbOfFin: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

Finset.orderIsoOfFin: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

Finset.prod: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.exact_completion_gap_point, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_perturbation, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.perspective_quadratic_mix, SparseCompletion.positive_score_call_identity, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.response_le_exploitability, SparseCompletion.shifted_call_antitone, SparseCompletion.variable_core_interval_completion_iff.

Finset.range: SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

Finset.weightedVSub: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

Finset.weightedVSubOfPoint: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

Fintype: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.exact_completion_gap_point, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_perturbation, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.positive_score_call_identity, SparseCompletion.positive_score_threshold, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.response_le_exploitability, SparseCompletion.shifted_call_antitone, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff.

Fintype.card: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.clone_support_card, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

FloorSemiring: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.unit_mass_grid_bound.

InfSet: SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

IsClosed: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff.

IsCompact: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff.

LinearMap: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

LinearOrder: SparseCompletion.endpoint_bounds_from_order, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_value_ordered_interval_stability.

Module.finrank: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

NNReal.sqrt: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.unit_mass_grid_bound.

Nat.ceil: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.unit_mass_grid_bound.

Real.sqrt: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.unit_mass_grid_bound.

Real.toNNReal: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.unit_mass_grid_bound.

RelEmbedding: SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

Set.Icc: SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

Set.image: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

Set.prod: SparseCompletion.exploitability_continuous, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

StarConvex: SparseCompletion.exact_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff.

Submodule.span: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

convexHull: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.

vectorSpan: SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_joint_support_upper.


Reviewed additional usage for Fintype: SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative.

Reviewed additional usage for Finset: SparseCompletion.aggregate_clones_mass.

Reviewed additional usage for Fintype.card: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares.

Reviewed additional usage for Finset.Nonempty: SparseCompletion.positive_score_threshold.

The actual exploitability function is Finset.univ.sup' of all row responses with a genuine universal-set nonemptiness proof from the nonempty action type. Finset.sup' and Finset.Nonempty therefore also cover SparseCompletion.exploitability_le_iff, SparseCompletion.response_le_exploitability, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_continuous, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_support_value_ordered_stability. This is a row supremum, distinct from the earlier interval-loss maximum; both are genuine attained finite extrema.


## Rational certificates, actual support enumeration, and nonemptiness

### Exact retained source src/Init/Data/Rat/Basic.lean

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean

Source SHA256 30b77ea0918aa986f6617bef4ad99a8d79cd538a714c9f05134bcb6a5e490cc8; Git blob 9722e2373e6d49b7ec3e635a6125af895c9940b0.

```lean
/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L27-L46

```lean
/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable
@[suggest_for ℚ]
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq, Hashable


```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L100-L117

```lean
Construct a rational number from a numerator and denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized, and returns
zero if `den` is zero.
-/
def mkRat (num : Int) (den : Nat) : Rat :=
  if den_nz : den = 0 then { num := 0 } else Rat.normalize num den den_nz

namespace Rat

/-- Embedding of `Int` in the rational numbers. -/
def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right _ }

instance : NatCast Rat where
  natCast n := ofInt n
instance : IntCast Rat := ⟨ofInt⟩

instance : OfNat Rat n := ⟨n⟩

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L140-L161

```lean

/-- Rational number strictly less than relation, as a `Bool`. -/
protected def blt (a b : Rat) : Bool :=
  if a.num < 0 && 0 ≤ b.num then
    true
  else if a.num = 0 then
    0 < b.num
  else if 0 < a.num && b.num ≤ 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den

instance : LT Rat := ⟨(·.blt ·)⟩

instance (a b : Rat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

instance : LE Rat := ⟨fun a b => b.blt a = false⟩

instance (a b : Rat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = false))

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L166-L185

```lean
/-- Multiplication of rational numbers. (This definition is `@[irreducible]` because you don't
want to unfold it. Use `Rat.mul_def` instead.) -/
@[irreducible] protected def mul (a b : Rat) : Rat :=
  let g1 := Nat.gcd a.num.natAbs b.den
  let g2 := Nat.gcd b.num.natAbs a.den
  { num := a.num.divExact g1 (normalize.dvd_num rfl) * b.num.divExact g2 (normalize.dvd_num rfl)
    den := a.den.divExact g2 (normalize.dvd_den rfl) * b.den.divExact g1 (normalize.dvd_den rfl)
    den_nz := Nat.ne_of_gt <| Nat.mul_pos
      (Nat.div_gcd_pos_of_pos_right _ a.den_pos) (Nat.div_gcd_pos_of_pos_right _ b.den_pos)
    reduced := by
      simp only [Int.divExact_eq_tdiv, Int.natAbs_mul, Int.natAbs_tdiv, Nat.coprime_mul_iff_left]
      refine ⟨Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩, Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩⟩
      · exact a.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ b.den_pos)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ a.den_pos)
      · exact b.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..) }

instance : Mul Rat := ⟨Rat.mul⟩

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L250-L282

```lean
  · have := (H1 bd).1 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.symm.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| b.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (be ▸ Nat.dvd_mul_right ..)

/--
Addition of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.add_def` instead.)
-/
@[irreducible] protected def add (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := add.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den + b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) + b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := add.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Add Rat := ⟨Rat.add⟩

/-- Negation of rational numbers. -/
@[implicit_reducible]
protected def neg (a : Rat) : Rat :=
  { a with num := -a.num, reduced := by rw [Int.natAbs_neg]; exact a.reduced }

instance : Neg Rat := ⟨Rat.neg⟩

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L291-L311

```lean

/-- Subtraction of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.sub_def` instead.)
-/
@[irreducible] protected def sub (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := sub.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den - b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) - b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := sub.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Sub Rat := ⟨Rat.sub⟩

```

### Exact retained source Mathlib/Algebra/Field/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean

Source SHA256 341e5bbbc77690b9cce20dd460d0a4c22138beea4ed9e10cc100c4d4a2db6152; Git blob c7cfb7246b4896ec3fc910efbfdeb50261baddeb.

```lean
/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean#L70-L75

```lean

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionRing` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean#L134-L154

```lean
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : ℚ≥0) (a : K) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected ratCast_def (q : ℚ) : (Rat.cast q : K) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Unless there is a risk of a `Module ℚ _` instance diamond, write `qsmul := _`. This will set
  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : ℚ → K → K
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : ℚ) (x : K) : qsmul a x = Rat.cast a * x := by intros; rfl


```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/Defs.lean#L196-L204

```lean

end NNRat

namespace Rat
variable [DivisionRing K]

lemma cast_def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _

lemma cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a / b := cast_def _

```

### Exact retained source Mathlib/Basic/Real/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Real/Basic.lean

Source SHA256 b10f715c299e6c3f468e916cad97620e921dc432e31269217954d94191fc7829; Git blob 3f5de911ff81bf5a8a6dc2e3dbfe8a4a7beec8f3.

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Real/Basic.lean#L161-L169

```lean
instance instNatCast : NatCast ℝ where natCast n := ⟨n⟩
instance instIntCast : IntCast ℝ where intCast z := ⟨z⟩
instance instNNRatCast : NNRatCast ℝ where nnratCast q := ⟨q⟩
instance instRatCast : RatCast ℝ where ratCast q := ⟨q⟩

lemma ofCauchy_natCast (n : ℕ) : (⟨n⟩ : ℝ) = n := rfl
lemma ofCauchy_intCast (z : ℤ) : (⟨z⟩ : ℝ) = z := rfl
lemma ofCauchy_nnratCast (q : ℚ≥0) : (⟨q⟩ : ℝ) = q := rfl
lemma ofCauchy_ratCast (q : ℚ) : (⟨q⟩ : ℝ) = q := rfl

```

### Exact retained source Mathlib/Data/Rat/Cast/CharZero.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/CharZero.lean

Source SHA256 a0cf8d3fd177656c086c13e1de2c9065d0ae898cc635acde1e5d877c46d3c5eb; Git blob 4bc491d3b1dafebc5cf20a5fc503bb87a51f5bfe.

```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/CharZero.lean#L20-L64

```lean

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : ℚ}

@[stacks 09FR "Characteristic zero case."]
lemma cast_injective : Injective ((↑) : ℚ → α)
  | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by
    have d₁a : (d₁ : α) ≠ 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) ≠ 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk_eq_divInt, mk_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero _ (by simpa), cast_divInt_of_ne_zero _ (by simpa)] at h
    norm_cast at h
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq,
      ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_natCast d₁,
      ← Int.cast_mul, ← Int.cast_natCast d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0]
      at h

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 := cast_injective.eq_iff' cast_zero
lemma cast_ne_zero : (p : α) ≠ 0 ↔ p ≠ 0 := cast_eq_zero.ne

@[simp, norm_cast] lemma cast_add (p q : ℚ) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

@[simp, norm_cast] lemma cast_sub (p q : ℚ) : ↑(p - q) = (p - q : α) :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

@[simp, norm_cast] lemma cast_mul (p q : ℚ) : ↑(p * q) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

variable (α) in
/-- Coercion `ℚ → α` as a `RingHom`. -/
@[implicit_reducible]
def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ → α) := rfl

@[simp, norm_cast] lemma cast_inv (p : ℚ) : ↑(p⁻¹) = (p⁻¹ : α) := map_inv₀ (castHom α) _
@[simp, norm_cast] lemma cast_div (p q : ℚ) : ↑(p / q) = (p / q : α) := map_div₀ (castHom α) ..

```

### Exact retained source Mathlib/Data/Rat/Cast/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/Order.lean

Source SHA256 7168364a994bf3fa35b898925ea574614748a9976df00e7bfd4b27cab0a3a2a6; Git blob ae4592f3acfb55a28a8f1cc7826d904f941e2717.

```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/Order.lean#L29-L54

```lean
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem cast_pos_of_pos (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]
theorem cast_strictMono : StrictMono ((↑) : ℚ → K) := fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]
theorem cast_mono : Monotone ((↑) : ℚ → K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono

@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le

@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt

@[simp] lemma cast_nonneg : 0 ≤ (q : K) ↔ 0 ≤ q := by norm_cast

@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast

```

### Exact retained source Mathlib/Data/Rat/Cast/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/Defs.lean

Source SHA256 110a63943b322f70b41bf277ee664ae602dbe6a7d4def27ae6568c2856101f30; Git blob b4b3794a6319462865b7ec095747392d963d4481.

```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Cast/Defs.lean#L174-L177

```lean
  · push_cast
    exact mul_ne_zero hq hr

@[simp, norm_cast] lemma cast_neg (q : ℚ) : ↑(-q) = (-q : α) := by simp [cast_def, neg_div]

```

### Exact retained source src/Init/Prelude.lean

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean

Source SHA256 cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39; Git blob f87ee970af5149d74434f09a89aedff1a8fdb2d2.

```lean
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L832-L841

```lean
`Nonempty α` is a typeclass that says that `α` is not an empty type,
that is, there exists an element in the type. It differs from `Inhabited α`
in that `Nonempty α` is a `Prop`, which means that it does not actually carry
an element of `α`, only a proof that *there exists* such an element.
Given `Nonempty α`, you can construct an element of `α` *nonconstructively*
using `Classical.choice`.
-/
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α

```

### Exact retained source Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

Source SHA256 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7; Git blob 866ef6ab673f737a4ffbb7b2138402d5c76e6c05.

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

### Exact retained source Mathlib/Data/Finset/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean

Source SHA256 ac132a546c19ca9e9ec46f864faae346c2c613c8bd7123bb0807c4ad630c302d; Git blob e94299ba14677e4193e7004cf77bf70c1ca6e065.

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean#L98-L118

```lean
/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
instance : SetLike (Finset α) α where
  coe s := {a | a ∈ s.1}
  coe_injective s₁ s₂ h := (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).2 <| Set.ext_iff.mp h

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl

-- If https://github.com/leanprover/lean4/issues/2678 is resolved-
-- this can be changed back to an `Iff`, but for now we would like `dsimp` to use it.
@[simp, grind =]
theorem mem_val {a : α} {s : Finset α} : (a ∈ s.1) = (a ∈ s) := rfl

@[simp, grind =]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl

instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean#L174-L181

```lean
  PiFinsetCoe.canLift ι (fun _ => α) s

instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a ∈ s where
  prf a ha := ⟨⟨a, ha⟩, rfl⟩

@[norm_cast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl

```

### Exact retained source Mathlib/Data/SetLike/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/SetLike/Basic.lean

Source SHA256 514b079e1db7bfbecf7a49c52be49150fa365ab9a8fe370a4a52aae465698598; Git blob 9bd1bb78940e58836f654fc5688a9b4d4c4b4c5a.

```lean
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/SetLike/Basic.lean#L120-L126

```lean
instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

```

### Exact retained source Mathlib/Data/Fintype/Sets.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sets.lean

Source SHA256 87b401f8e6bf02de9250adba00dcb1de4157d55e286f6e627d01639fe2b2ef9a; Git blob 81672c76f6ea0ec10b76b09a4422bdb9312e9e90.

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sets.lean#L222-L231

```lean

/-! ### `Fintype (s : Finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Sets.lean#L245-L249

```lean
instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s

```

### Exact retained source Mathlib/Data/Finset/Attach.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Attach.lean

Source SHA256 4fdb01a7ff510914f4940e38fda5281f89b3fc59802d033bf833edef571f3de6; Git blob cd5f80fca89b7e0609388f6ee97977b4eca0d511.

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Attach.lean#L44-L58

```lean
/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩

@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl

@[simp, grind ←]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  Multiset.mem_attach _

@[simp, norm_cast]
theorem coe_attach (s : Finset α) : (s.attach : Set s) = Set.univ := by ext; simp

```

### Exact retained source Mathlib/Data/Multiset/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Defs.lean

Source SHA256 418e9f8cfefe7e643c58737d3986e6910f0cb818640a3b10ff97fe9d27d56ed3; Git blob 0d0fe151e7b0321cae4626f575644f6bd8bbe1d7.

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Defs.lean#L283-L294

```lean
/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun _a => id

@[simp]
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl

@[simp]
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  Quot.inductionOn s fun _l => List.mem_attach _

```

### Exact retained source Mathlib/Data/Set/Finite/Lemmas.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Finite/Lemmas.lean

Source SHA256 c91596535840063fb0507849f4bdc53d44a49e389739af998cd2902c17a8d35c; Git blob de41c17e1d3056674b274a6b3e695a9e20c87a25.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Finite/Lemmas.lean#L73-L80

```lean

@[to_dual]
theorem exists_min_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_min_image f ⟨x, h1.mem_toFinset.2 hx⟩


```

### Batteries RatCast, separate pinned dependency

https://github.com/leanprover-community/batteries/blob/ed9b316aabe389fec1ef43c3326ab48c7e59be42/Batteries/Classes/RatCast.lean

Source SHA256 2d2f0265802ab69e891924f62d1ddca1b82c303027dfa0ef3453bea37577e7b9; Git blob b2df7c7304c219d3b812a2b800154d03007f9110.

```lean
/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Gabriel Ebner
-/
```

https://github.com/leanprover-community/batteries/blob/ed9b316aabe389fec1ef43c3326ab48c7e59be42/Batteries/Classes/RatCast.lean#L10-L15

```lean
/-- Type class for the canonical homomorphism `Rat → K`. -/
class RatCast (K : Type u) where
  /-- The canonical homomorphism `Rat → K`. -/
  protected ratCast : Rat → K

instance : RatCast Rat where ratCast n := n

```

https://github.com/leanprover-community/batteries/blob/ed9b316aabe389fec1ef43c3326ab48c7e59be42/Batteries/Classes/RatCast.lean#L17-L26

```lean
/-- Canonical homomorphism from `Rat` to a division ring `K`.
This is just the bare function in order to aid in creating instances of `DivisionRing`. -/
@[coe, reducible, match_pattern] protected def Rat.cast {K : Type u} [RatCast K] : Rat → K :=
  RatCast.ratCast

-- see note [coercion into rings]
instance [RatCast K] : CoeTail Rat K where coe := Rat.cast

-- see note [coercion into rings]
instance [RatCast K] : CoeHTCT Rat K where coe := Rat.cast

```

### Exact retained source Mathlib/Data/Rat/Init.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Init.lean

Source SHA256 8bf4701007955ed168463dde3a8a30fe19d3ea979aec1dfd128d4ef8858aa1a2; Git blob 1583d46e237792c89bf490d4b1684ce8f4b73054.

```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Init.lean#L8-L24

```lean
public import Mathlib.Data.Nat.Notation
public import Batteries.Classes.RatCast

/-!
# Basic definitions around the rational numbers

This file declares `ℚ` notation for the rationals and defines the nonnegative rationals `ℚ≥0`.

This file is eligible to upstreaming to Batteries.
-/

@[expose] public section

@[inherit_doc] notation "ℚ" => Rat

/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}

```

### Rat.castRec material account

Default rational-to-division-ring recipe is the integer numerator divided by its nonzero natural denominator. Batteries RatCast supplies the selected map/coercions. Real overrides the default recipe with its Cauchy-real injection. The numerator/denominator formula, injectivity, order reflection and arithmetic preservation are proved contracts, not definitional equality of the Real constructor. Compiler Rat data, reduced arithmetic and lawful decidability are retained separately; finite support uses its actual attach enumeration.

Used by: SparseCompletion.RationalCertificate.accepted_full_game, SparseCompletion.RationalCertificate.check_iff_full_rows.

### Set.Nonempty material account

There exists an actual member of the set; compactness alone does not supply one. Distinct from the compiler Nonempty typeclass and from Inhabited/default data. The exact existential definition and separate actual witness hypotheses/constructions are retained.

Affected declarations are listed in the final coverage table below.



## Natural floor and finite allocation-grid audit

### Mathlib/Algebra/Order/Floor/Defs.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean

Source SHA256 f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L56-L71

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L114-L119

```lean
variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor


```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L208-L242

```lean
open scoped Classical in
private noncomputable def floorAux
    {α} [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {x : α}
    (below : ∃ n : ℤ, n ≤ x) (above : ∃ n : ℤ, x ≤ n) :
    {n : ℤ // n ≤ x ∧ ∀ m : ℤ, m ≤ x → m ≤ n} := by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· ≤ x)) n.1 (fun m hm ↦ ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2

/-- See `exists_floor` for a variant which instead assumes an `Archimedean` ring. -/
theorem exists_floor'
    {α} [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] (x : α)
    (below : ∃ n : ℤ, n ≤ x) (above : ∃ n : ℤ, x ≤ n) :
    ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : α) ≤ x := by
  refine ⟨_, fun n ↦ ⟨?_, (floorAux below above).2.2 _⟩⟩
  rw [← Int.cast_le (R := α)]
  exact le_trans' (floorAux below above).2.1

/-- Construct a `FloorRing` instance noncomputably, from the hypothesis that every element is
bounded above by a natural number. -/
@[no_expose, instance_reducible]
noncomputable def FloorRing.ofBounded
    (α) [Ring α] [LinearOrder α] [IsOrderedRing α] [Nontrivial α]
    (bounded : ∀ x : α, ∃ n : ℕ, x ≤ n) : FloorRing α :=
  have below (x : α) : ∃ n : ℤ, n ≤ x := by
    obtain ⟨n, hn⟩ := bounded (-x)
    use -n
    simpa [neg_le]
  have above (x : α) : ∃ n : ℤ, x ≤ n := by
    obtain ⟨n, hn⟩ := bounded x
    use n
    exact_mod_cast hn
  .ofFloor _ _ fun n x ↦ (Classical.choose_spec (exists_floor' x (below x) (above x)) n).symm


```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L341-L351

```lean

-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_lt.mpr (ha.trans_eq Int.cast_zero.symm)).le
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

```

### Mathlib/Algebra/Order/Floor/Semiring.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean

Source SHA256 1b0e45f02a914287979a2f39feb3f5b4808bff05f49e5a998e718168c4e36efb

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean#L36-L63

```lean

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

section floor

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha

theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by rw [Nat.cast_one]

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : R) ≤ a :=
  (le_floor_iff ha).1 le_rfl

theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_ge fun h' => (le_floor h').not_gt h

theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast lt_of_floor_lt h

theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _

@[bound]
theorem lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean#L82-L95

```lean

theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

@[gcongr]
theorem floor_mono : Monotone (floor : R → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

@[bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := floor_mono hab

```

### Mathlib/Algebra/Order/Archimedean/Basic.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Basic.lean

Source SHA256 bf2b863c793c5fae4baaec4722b94771c1feb00947104b6965fb13f8a66962da

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Basic.lean#L477-L483

```lean
/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
@[instance_reducible]
noncomputable def Archimedean.floorRing (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] : FloorRing R :=
  .ofBounded _ exists_nat_ge


```

### Mathlib/Algebra/Order/Archimedean/Real/Basic.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean

Source SHA256 1c03e3aecbfa3739e79ae8ebfd33b6100781d4c90e6475677cdcff4487e972d1

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Real/Basic.lean#L30-L38

```lean

instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

```

### Mathlib/Data/Fintype/Pi.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean

Source SHA256 3621d016ef00906a9538347e3565bc44f5fe22210006ba64009b183c8ff6338f

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean#L26-L45

```lean
variable [DecidableEq α] [Fintype α] {γ δ : α → Type*} {s : ∀ a, Finset (γ a)}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp, grind =]
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a := by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean#L132-L143

```lean

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.instFintype {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] : Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]
theorem Fintype.piFinset_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl

```

### Mathlib/Data/Finset/Pi.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Pi.lean

Source SHA256 f218ce708938f20007a6662a41c52aab6453f666bea3766197ccf1d26c1f3418

```lean
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Pi.lean#L47-L58

```lean
/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `β a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]
theorem pi_val (s : Finset α) (t : ∀ a, Finset (β a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl

@[simp, grind =]
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (β a)} {f : ∀ a ∈ s, β a} :

```

### Mathlib/Data/Fintype/BigOperators.lean exact floor/enumeration contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean

Source SHA256 b9a6354ebff5fcd22fb1ddb7992682a404ec44c8ee42d519177f17d1d5a239e9

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/BigOperators.lean#L198-L202

```lean
-- TODO: this is a basic theorem about `Fintype.card`,
-- and ideally could be moved to `Mathlib/Data/Fintype/Card.lean`.
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  simp

```

### Material Nat.floor account

Nat.floor selects the FloorSemiring.floor field and is natural-valued: it is zero on negative reals. It is the greatest natural below a nonnegative input; the contract floor(x)<=x requires x>=0. The next-integer bound x<floor(x)+1 and monotonicity hold for all reals. Actual Real floor is noncomputable via Archimedean FloorRing construction and then Int.toNat; these mathematical rounding lemmas are not an executable Real-floor algorithm. Finite allocation maps are actual functions from the anchor index type to the finite ordinal, enumerated by Pi.instFintype/Fintype.piFinset, whose cardinal is N^(card anchors).

FloorSemiring.floor and its Galois connection select the natural floor, zero on negative inputs. Actual Real FloorRing uses an Archimedean choice construction and the Nat floor is its Int.toNat truncation; mathematical rounding is not claimed executable on arbitrary Reals. Pi.instFintype enumerates genuine finite functions by Fintype.piFinset; its cardinality is proved, not a runtime assertion.

## Conditional rational bisection order and finite-width evidence

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean

Source SHA256 9b75e423f4425994dec847788cbcf1a510fce43c1c69facba3f9cdef50ed37d6

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean#L56-L63

```lean

section MonotoneDef

variable [Preorder α] [Preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/Prop.lean

Source SHA256 a68666f5228676d4cc8f5e30e46b072952fc626e6fa73af493fe28f61e52dbb1

```lean
/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Defs/Prop.lean#L27-L33

```lean
/-- Propositions form a complete Boolean algebra, where the `≤` relation is given by implication. -/
instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩

@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (· → ·) :=
  rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Defs.lean

Source SHA256 792d8e81ef492132ffe4cbd31ad9cfa0cf4d2a215b47acb86f1240bba0a6525c

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Defs.lean#L30-L35

```lean
/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (R) [AddCommMonoid R] [PartialOrder R] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : R) {y : R}, 0 < y → ∃ n : ℕ, x ≤ n • y

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Defs.lean#L73-L77

```lean
section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_nat_gt (x : R) : ∃ n : ℕ, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Basic.lean

Source SHA256 bf2b863c793c5fae4baaec4722b94771c1feb00947104b6965fb13f8a66962da

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Archimedean/Basic.lean#L309-L351

```lean
section LinearOrderedField
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_nat_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

theorem archimedean_iff_nat_le : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_int_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

theorem archimedean_iff_int_le : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_rat_lt : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x < q where
  mp _ x :=
    let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x ↦
    let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h <| mod_cast Nat.le_ceil _⟩

theorem archimedean_iff_rat_le : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

```

### Monotone predicate account

For rational thresholds and proposition-valued P, a<=b and P(a) imply P(b). Monotone uses source/target preorder. Target Prop.le is implication, not numerical comparison or a decidability assertion; predicate decision procedure remains an explicit DecidablePred parameter.

### Final affected-declaration coverage

Literal uses and stated proof-dependency expansions; finite-function cardinality and rational certificates carry no inferred runtime claim.

**Fintype**: SparseCompletion.RationalCertificate.accepted_full_game, SparseCompletion.RationalCertificate.check_iff, SparseCompletion.RationalCertificate.check_iff_full_rows, SparseCompletion.RationalCertificate.reject_omitted_violation, SparseCompletion.RationalCertificate.rows_iff, SparseCompletion.RationalCertificate.support_card_le, SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.allocation_grid_card, SparseCompletion.allocation_grid_nonempty, SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_in_grid, SparseCompletion.allocation_rounding_mass, SparseCompletion.allocation_rounding_preserves_floors, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.anchor_response_mix, SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.balancedLength_cube_sum, SparseCompletion.balancedLength_mass, SparseCompletion.balanced_finite_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.binIndex_val, SparseCompletion.bin_affine_mean, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_affine_moment, SparseCompletion.bin_compressed_calls, SparseCompletion.bin_compressed_mass, SparseCompletion.bin_compressed_moment, SparseCompletion.bin_compressed_nonneg, SparseCompletion.bin_compressed_quadratic_loss, SparseCompletion.bin_compressed_support, SparseCompletion.bin_odd_support, SparseCompletion.bin_quadratic_loss_bounds, SparseCompletion.bin_quadratic_loss_identity, SparseCompletion.bin_quadratic_parity_identity, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_game_witness, SparseCompletion.binned_mass, SparseCompletion.binned_middle_injective, SparseCompletion.binned_middle_positive, SparseCompletion.binned_moment, SparseCompletion.binned_nonneg, SparseCompletion.binned_odd_game_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_odd_support_exact, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_support, SparseCompletion.binned_support_lower, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_uniform_score_mean, SparseCompletion.block_response_bounds_iff, SparseCompletion.block_support_card, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.bounded_two_anchor_minimum_share_rigidity, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.compact_block_certificate_iff, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.completion_cuts_necessary, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.core_witness_interval, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_iff_call_bound, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.exploitability_bounded_above, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_nonnegative, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_strategy_distance, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_grid_implication, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.floor_strategies_nonempty, SparseCompletion.floor_strategy_coordinate_bounds, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_recovered_score_moment, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.linear_repertoire_convex, SparseCompletion.nonnegative_mass_zero, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.partition_game_witness, SparseCompletion.perspective_call_epigraph_iff, SparseCompletion.perspective_call_identity, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.positive_score_call_identity, SparseCompletion.positive_score_threshold, SparseCompletion.positive_target_full_support, SparseCompletion.prefix_cut_quadratic, SparseCompletion.prefix_exposing_identity, SparseCompletion.prefix_quadratic_mix, SparseCompletion.prefix_system_convex, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered, SparseCompletion.residual_projection_response_bound, SparseCompletion.response_guard, SparseCompletion.response_le_exploitability, SparseCompletion.response_perturbation, SparseCompletion.response_strategy_distance, SparseCompletion.score_lower_from_intervals, SparseCompletion.shifted_call_antitone, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.strict_prefix_rigidity, SparseCompletion.sum_bin_partition, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.supported_response_zero, SparseCompletion.threshold_is_score_prefix, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.transferred_residual_distance, SparseCompletion.transferred_residual_mass, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.two_anchor_total_support_card, SparseCompletion.two_core_anchor_shift, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_adjust, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.uniform_score_affine, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_target_cuts, SparseCompletion.uniform_target_score, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Finset**: SparseCompletion.RationalCertificate.accepted_full_game, SparseCompletion.RationalCertificate.b_on, SparseCompletion.RationalCertificate.check_iff, SparseCompletion.RationalCertificate.check_iff_full_rows, SparseCompletion.RationalCertificate.q_on, SparseCompletion.RationalCertificate.realB_omitted, SparseCompletion.RationalCertificate.realB_stored, SparseCompletion.RationalCertificate.realQ_off, SparseCompletion.RationalCertificate.reject_omitted_violation, SparseCompletion.RationalCertificate.rows_iff, SparseCompletion.RationalCertificate.support_card_le, SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.allocation_grid_card, SparseCompletion.allocation_grid_nonempty, SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_in_grid, SparseCompletion.allocation_rounding_mass, SparseCompletion.allocation_rounding_preserves_floors, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.anchor_response_mix, SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.balancedLength_cube_sum, SparseCompletion.balancedLength_mass, SparseCompletion.balanced_finite_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.binIndex_val, SparseCompletion.bin_affine_mean, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_affine_moment, SparseCompletion.bin_compressed_calls, SparseCompletion.bin_compressed_mass, SparseCompletion.bin_compressed_moment, SparseCompletion.bin_compressed_nonneg, SparseCompletion.bin_compressed_quadratic_loss, SparseCompletion.bin_compressed_support, SparseCompletion.bin_odd_support, SparseCompletion.bin_quadratic_loss_bounds, SparseCompletion.bin_quadratic_loss_identity, SparseCompletion.bin_quadratic_parity_identity, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_game_witness, SparseCompletion.binned_mass, SparseCompletion.binned_middle_injective, SparseCompletion.binned_middle_positive, SparseCompletion.binned_moment, SparseCompletion.binned_nonneg, SparseCompletion.binned_odd_game_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_odd_support_exact, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_support, SparseCompletion.binned_support_lower, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_uniform_score_mean, SparseCompletion.block_response_bounds_iff, SparseCompletion.block_support_card, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.bounded_two_anchor_minimum_share_rigidity, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.compactCompletion_bounds, SparseCompletion.compactCompletion_skew, SparseCompletion.compact_block_certificate_iff, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.completion_cuts_necessary, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.core_witness_interval, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_iff_call_bound, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.exploitability_bounded_above, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_nonnegative, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_strategy_distance, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_grid_implication, SparseCompletion.finite_linear_mix, SparseCompletion.finite_mass_mix, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.floor_strategies_nonempty, SparseCompletion.floor_strategy_coordinate_bounds, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_recovered_score_moment, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.linear_repertoire_convex, SparseCompletion.nonnegative_mass_zero, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.partition_game_witness, SparseCompletion.perspective_call_epigraph_iff, SparseCompletion.perspective_call_identity, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.perspective_quadratic_mix, SparseCompletion.positive_score_call_identity, SparseCompletion.positive_score_threshold, SparseCompletion.positive_target_full_support, SparseCompletion.prefix_cut_quadratic, SparseCompletion.prefix_exposing_identity, SparseCompletion.prefix_quadratic_mix, SparseCompletion.prefix_system_convex, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered, SparseCompletion.residual_projection_response_bound, SparseCompletion.response_guard, SparseCompletion.response_le_exploitability, SparseCompletion.response_perturbation, SparseCompletion.response_strategy_distance, SparseCompletion.score_lower_from_intervals, SparseCompletion.shifted_call_antitone, SparseCompletion.skew_weighted_sum, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.strict_prefix_rigidity, SparseCompletion.sum_bin_partition, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.supported_response_zero, SparseCompletion.threshold_is_score_prefix, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.transferred_residual_distance, SparseCompletion.transferred_residual_mass, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.two_anchor_total_support_card, SparseCompletion.two_core_anchor_shift, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_adjust, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.uniform_score_affine, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_target_cuts, SparseCompletion.uniform_target_score, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Finset.prod**: SparseCompletion.RationalCertificate.accepted_full_game, SparseCompletion.RationalCertificate.check_iff, SparseCompletion.RationalCertificate.check_iff_full_rows, SparseCompletion.RationalCertificate.reject_omitted_violation, SparseCompletion.RationalCertificate.rows_iff, SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.aggregate_clones_mass, SparseCompletion.aggregate_clones_mono, SparseCompletion.aggregate_clones_nonnegative, SparseCompletion.allocation_grid_nonempty, SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_in_grid, SparseCompletion.allocation_rounding_mass, SparseCompletion.allocation_rounding_preserves_floors, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.anchor_response_mix, SparseCompletion.anchor_response_of_perspective, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.balancedLength_cube_sum, SparseCompletion.balancedLength_mass, SparseCompletion.balanced_finite_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.binIndex_val, SparseCompletion.bin_affine_mean, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_affine_moment, SparseCompletion.bin_compressed_calls, SparseCompletion.bin_compressed_mass, SparseCompletion.bin_compressed_moment, SparseCompletion.bin_compressed_nonneg, SparseCompletion.bin_compressed_quadratic_loss, SparseCompletion.bin_compressed_support, SparseCompletion.bin_odd_support, SparseCompletion.bin_quadratic_loss_bounds, SparseCompletion.bin_quadratic_loss_identity, SparseCompletion.bin_quadratic_parity_identity, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_game_witness, SparseCompletion.binned_mass, SparseCompletion.binned_middle_injective, SparseCompletion.binned_middle_positive, SparseCompletion.binned_moment, SparseCompletion.binned_nonneg, SparseCompletion.binned_odd_game_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_odd_support_exact, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_support, SparseCompletion.binned_support_lower, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_uniform_score_mean, SparseCompletion.block_response_bounds_iff, SparseCompletion.block_support_card, SparseCompletion.bounded_two_anchor_fixed_share_rigidity, SparseCompletion.bounded_two_anchor_minimum_share_rigidity, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clone_support_card, SparseCompletion.cloned_anchor_response, SparseCompletion.cloned_response_anchor, SparseCompletion.cloned_response_bounds_iff, SparseCompletion.cloned_response_residual, SparseCompletion.cloned_score, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.compact_block_certificate_iff, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.completion_cuts_necessary, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.core_witness_interval, SparseCompletion.cuts_dual_bound, SparseCompletion.cuts_iff_call_bound, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.exploitability_bounded_above, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_nonnegative, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_strategy_distance, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_grid_implication, SparseCompletion.finite_linear_mix, SparseCompletion.finite_mass_mix, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.floor_strategies_nonempty, SparseCompletion.floor_strategy_coordinate_bounds, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_moment_mix, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_recovered_score_moment, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.linear_repertoire_convex, SparseCompletion.nonnegative_mass_zero, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.partition_game_witness, SparseCompletion.perspective_call_epigraph_iff, SparseCompletion.perspective_call_identity, SparseCompletion.perspective_cut_system_convex, SparseCompletion.perspective_cuts_iff, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.perspective_cuts_mix, SparseCompletion.perspective_moment_zero, SparseCompletion.perspective_quadratic_mix, SparseCompletion.positive_score_call_identity, SparseCompletion.positive_target_full_support, SparseCompletion.prefix_cut_quadratic, SparseCompletion.prefix_exposing_identity, SparseCompletion.prefix_quadratic_mix, SparseCompletion.prefix_system_convex, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_support_card, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.residual_projection_response_bound, SparseCompletion.response_guard, SparseCompletion.response_le_exploitability, SparseCompletion.response_perturbation, SparseCompletion.response_strategy_distance, SparseCompletion.score_lower_from_intervals, SparseCompletion.shifted_call_antitone, SparseCompletion.skew_weighted_sum, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.strict_prefix_rigidity, SparseCompletion.sum_bin_partition, SparseCompletion.supported_response_zero, SparseCompletion.threshold_is_score_prefix, SparseCompletion.tight_prefix_completion_unique, SparseCompletion.transferred_residual_distance, SparseCompletion.transferred_residual_mass, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_fixed_share_uniqueness, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.two_anchor_total_support_card, SparseCompletion.two_core_anchor_shift, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_adjust, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniform_exposing_weight, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.uniform_score_affine, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_target_cuts, SparseCompletion.uniform_target_score, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_two_anchor_dense, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Set.Icc**: SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clipped_observation_interval, SparseCompletion.cuts_iff_call_bound, SparseCompletion.cuts_iff_positive_thresholds, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_grid_implication, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.floor_strategies_compact, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_system_iff_threshold_system, SparseCompletion.joint_anchor_support_order, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.perspective_cuts_iff_candidate_thresholds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.variable_core_interval_completion_iff.

**Nat.ceil**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.double_grid_support_upper, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.gridSize_bound, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.unit_mass_grid_bound.

**FloorSemiring**: SparseCompletion.allocation_grid_card, SparseCompletion.allocation_grid_nonempty, SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_in_grid, SparseCompletion.allocation_rounding_mass, SparseCompletion.allocation_rounding_preserves_floors, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.double_grid_support_upper, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.gridSize_bound, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.rounded_allocation_finite_grid, SparseCompletion.rounded_anchor_bounds, SparseCompletion.rounded_anchor_grid_index, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.unit_mass_grid_bound.

**NNReal.sqrt**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.double_grid_support_upper, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.gridSize_bound, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.residual_rate_from_inverse_square, SparseCompletion.uncertainty_rate_comparison, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.unit_mass_grid_bound.

**Real.sqrt**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.double_grid_support_upper, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.gridSize_bound, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.residual_rate_from_inverse_square, SparseCompletion.uncertainty_rate_comparison, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.unit_mass_grid_bound.

**Real.toNNReal**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.double_grid_support_upper, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_anchor_gap_monotone, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasibility_monotone, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.gridSize_bound, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_epigraph_iff, SparseCompletion.interval_gap_recovered_exact_point, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.residual_rate_from_inverse_square, SparseCompletion.uncertainty_rate_comparison, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.unit_mass_grid_bound.

**Convex**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.interval_perspective_cut_system_convex, SparseCompletion.interval_perspective_system_convex, SparseCompletion.interval_system_repertoire_convex, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.linear_repertoire_convex, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.perspective_cut_system_convex, SparseCompletion.prefix_system_convex, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.residual_linear_repertoire_convex, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff.

**StarConvex**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_convex, SparseCompletion.linear_repertoire_convex, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.prefix_system_convex, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff.

**convexHull**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**AffineIndependent**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**Finset.weightedVSub**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**Finset.weightedVSubOfPoint**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**vectorSpan**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**Submodule.span**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**Module.finrank**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments.

**Finset.card**: SparseCompletion.RationalCertificate.support_card_le, SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.allocation_grid_card, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.balanced_finite_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.bin_compressed_support, SparseCompletion.bin_odd_support, SparseCompletion.binned_finite_game_witness, SparseCompletion.binned_game_witness, SparseCompletion.binned_mass, SparseCompletion.binned_odd_game_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_odd_support_exact, SparseCompletion.binned_support, SparseCompletion.binned_support_lower, SparseCompletion.block_support_card, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clone_support_card, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_observations_bounded, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.cloned_witness_aggregates, SparseCompletion.core_witness_interval, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.partition_game_witness, SparseCompletion.positive_target_full_support, SparseCompletion.relabel_support_card, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.sum_bin_partition, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.two_anchor_total_support_card, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.variable_core_interval_completion_iff.

**Fintype.card**: SparseCompletion.aggregate_clone_lower, SparseCompletion.aggregate_clone_shares, SparseCompletion.allocation_grid_card, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.balanced_finite_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.bin_compressed_support, SparseCompletion.bin_odd_support, SparseCompletion.binned_finite_game_witness, SparseCompletion.binned_game_witness, SparseCompletion.binned_mass, SparseCompletion.binned_odd_game_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_odd_support_exact, SparseCompletion.binned_support, SparseCompletion.binned_support_lower, SparseCompletion.block_support_card, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.clone_support_card, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.core_witness_interval, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.finite_feature_compression, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.partition_game_witness, SparseCompletion.positive_target_full_support, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.sparse_cut_witness, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.sum_bin_partition, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.two_anchor_total_support_card, SparseCompletion.two_core_response_perturbation, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniform_core_dense, SparseCompletion.uniform_core_restore, SparseCompletion.uniform_core_support_exists, SparseCompletion.uniform_core_total_support_card, SparseCompletion.uniform_core_total_support_lower, SparseCompletion.uniform_exact_to_interval, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_interval_dense, SparseCompletion.uniform_interval_restore, SparseCompletion.uniform_interval_support_exists, SparseCompletion.uniform_interval_total_support_card, SparseCompletion.uniform_interval_total_support_lower, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_fixed_residual_positive, SparseCompletion.uniform_witness_residual_lower, SparseCompletion.uniform_witness_small_residual_positive, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniform_witness_total_support_card.

**IsCompact**: SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**IsClosed**: SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.support_budget_closed, SparseCompletion.support_restricted_compact, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Continuous**: SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exploitability_continuous, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.floor_strategies_compact, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_points_closed, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_matrices_compact, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**LinearMap**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**ContinuousLinearMap**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Set.image**: SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.completion_of_cuts_and_guards, SparseCompletion.cuts_weighted_completion, SparseCompletion.exact_completion_gap_point, SparseCompletion.exact_game_sparse_completion, SparseCompletion.exact_game_sparse_completion_extra_moments, SparseCompletion.exact_game_sparse_cut_certificate_extra_moments, SparseCompletion.exact_interval_completion_gap_point, SparseCompletion.exact_sparse_cut_witness_extra_moments, SparseCompletion.feasible_implies_gap_feasible, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.game_sparse_completion, SparseCompletion.game_sparse_completion_extra_moments, SparseCompletion.game_sparse_cut_certificate_extra_moments, SparseCompletion.gap_feasible_implies_relaxed_feasible, SparseCompletion.gap_infeasible_excludes_completion, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_point_completed_witness, SparseCompletion.gap_sparse_completed_witness, SparseCompletion.gap_sparse_point, SparseCompletion.gap_sparse_point_positive, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_gap_completed_witness, SparseCompletion.interval_gap_sparse_completed_witness, SparseCompletion.interval_perspective_completion_iff, SparseCompletion.joint_anchor_support_order, SparseCompletion.joint_anchor_support_order_general, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_cover_witness, SparseCompletion.normalized_exact_cover_witness, SparseCompletion.normalized_exact_sparse_witness, SparseCompletion.normalized_exact_sparse_witness_all_mass, SparseCompletion.normalized_exact_sparse_witness_extra_moments, SparseCompletion.normalized_exact_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_witness, SparseCompletion.normalized_gap_sparse_completed_witness, SparseCompletion.normalized_interval_gap_completed_witness, SparseCompletion.normalized_interval_gap_sparse_completed_witness, SparseCompletion.normalized_interval_perspective_iff, SparseCompletion.normalized_joint_support_upper, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_sparse_witness, SparseCompletion.normalized_sparse_witness_all_mass, SparseCompletion.normalized_sparse_witness_extra_moments, SparseCompletion.normalized_sparse_witness_extra_moments_all_mass, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_weak_cover_witness, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.repertoire_interval_completion_iff, SparseCompletion.sparse_cut_witness_extra_moments, SparseCompletion.variable_core_interval_completion_iff, SparseCompletion.weighted_completion_iff, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Finset.range**: SparseCompletion.uniform_exposing_weight, SparseCompletion.two_anchor_fixed_share_stability, SparseCompletion.two_anchor_minimum_share_stability, SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.two_anchor_total_support_card, SparseCompletion.uniform_sparse_upper_rate, SparseCompletion.uniform_witness_total_support_card, SparseCompletion.uniform_witness_dense, SparseCompletion.uniform_witness_support_exists, SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.cloned_uniform_dense, SparseCompletion.cloned_uniform_dense_full_game, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

**LocallyFiniteOrderBot**: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight.

**LocallyFiniteOrderTop**: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight.

**Finset.Ioi**: SparseCompletion.uniform_target_score, SparseCompletion.uniform_exposing_weight.

**Nat.find**: SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp.

**Nat.findX**: SparseCompletion.uniformMinimumTotalSupport_attained, SparseCompletion.uniformMinimumTotalSupport_le, SparseCompletion.uniformMinimumTotalSupport_zero, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.uniformMinimumResidualSupport_attained, SparseCompletion.uniformMinimumResidualSupport_le, SparseCompletion.uniformMinimumResidualSupport_zero, SparseCompletion.uniformMinimumResidualSupport_upper, SparseCompletion.uniformMinimumResidualSupport_fixed_sharp, SparseCompletion.uniformMinimumResidualSupport_natural_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_attained, SparseCompletion.uniformMinimumIntervalTotalSupport_lower, SparseCompletion.uniformMinimumIntervalTotalSupport_le, SparseCompletion.uniformMinimumIntervalTotalSupport_radius_zero, SparseCompletion.uniformMinimumIntervalTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_attained, SparseCompletion.uniformMinimumCoreTotalSupport_le, SparseCompletion.uniformMinimumCoreTotalSupport_lower, SparseCompletion.uniformMinimumCoreTotalSupport_radius_zero, SparseCompletion.uniformMinimumCoreTotalSupport_origin, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp.

**RelEmbedding**: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

**Finset.orderIsoOfFin**: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

**Finset.orderEmbOfFin**: SparseCompletion.finite_subset_quantization_bound, SparseCompletion.sparse_cumulative_quantization, SparseCompletion.uniform_fixed_share_support_lower, SparseCompletion.uniform_minimum_share_support_lower, SparseCompletion.uniform_fixed_share_inverse_square, SparseCompletion.uniform_minimum_share_inverse_square, SparseCompletion.uniform_total_support_lower, SparseCompletion.uniformMinimumTotalSupport_sharp, SparseCompletion.cloned_uniform_total_support_lower, SparseCompletion.joint_anchor_support_order.

**Equiv**: SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_calls, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.balanced_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_odd_game_witness, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_odd_support, SparseCompletion.binned_middle_positive, SparseCompletion.binned_middle_injective, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_relabel_on_anchor, SparseCompletion.cover_relabel_on_residual, SparseCompletion.relabel_intervals, SparseCompletion.relabel_mass, SparseCompletion.relabel_response, SparseCompletion.relabel_skew, SparseCompletion.relabel_support_card, SparseCompletion.split_skew_matrix, SparseCompletion.split_weights.

**finSigmaFinEquiv**: SparseCompletion.binIndex_val, SparseCompletion.sum_bin_partition, SparseCompletion.binned_nonneg, SparseCompletion.binned_support, SparseCompletion.binned_moment, SparseCompletion.binned_mass, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_score_mean, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.partition_game_witness, SparseCompletion.balanced_game_witness, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.balanced_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_odd_game_witness, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_odd_support, SparseCompletion.binned_middle_positive, SparseCompletion.binned_middle_injective, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact.

**Finset.sigma**: SparseCompletion.balanced_game_witness, SparseCompletion.binned_affine_moment, SparseCompletion.binned_call_contraction, SparseCompletion.binned_exposing_loss, SparseCompletion.binned_game_witness, SparseCompletion.binned_quadratic_loss, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.binned_uniform_score_mean, SparseCompletion.partition_game_witness, SparseCompletion.sum_bin_partition, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper, SparseCompletion.binned_finite_correction, SparseCompletion.binned_finite_game_witness, SparseCompletion.balanced_finite_game_witness, SparseCompletion.binned_game_completion_exact, SparseCompletion.binned_odd_game_witness, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_quadratic_loss_exact, SparseCompletion.binned_exposing_loss_exact, SparseCompletion.binned_odd_support, SparseCompletion.binned_middle_positive, SparseCompletion.binned_middle_injective, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact.

**Fin.revPerm**: SparseCompletion.balanced_game_witness, SparseCompletion.bin_call_compression, SparseCompletion.bin_call_compression_nonneg, SparseCompletion.bin_compressed_calls, SparseCompletion.binned_call_contraction, SparseCompletion.binned_game_witness, SparseCompletion.binned_uniform_cuts, SparseCompletion.binned_uniform_residual_completion, SparseCompletion.partition_game_witness, SparseCompletion.uniformMinimumCoreTotalSupport_sharp, SparseCompletion.uniformMinimumIntervalTotalSupport_sharp, SparseCompletion.uniform_binned_upper, SparseCompletion.uniform_core_uncertainty_upper.

**Finset.image**: SparseCompletion.binned_odd_game_witness, SparseCompletion.uniform_odd_midpoint_witness, SparseCompletion.binned_odd_support, SparseCompletion.binned_support_lower, SparseCompletion.binned_odd_support_exact, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered.

**Antitone**: SparseCompletion.threshold_is_score_prefix, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.normalized_known_anchor_conic_iff.

**Finset.Nonempty**: SparseCompletion.allocation_rounding_value_bound, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.cuts_iff_score_prefixes, SparseCompletion.exploitability_bounded_above, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_nonnegative, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_strategy_distance, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.known_anchor_conic_system_iff, SparseCompletion.known_anchor_prefix_characterization, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_known_anchor_conic_iff, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.positive_score_threshold, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_values_nonempty, SparseCompletion.response_le_exploitability, SparseCompletion.response_strategy_distance, SparseCompletion.threshold_is_score_prefix, SparseCompletion.weighted_completion_prefix_quadratic_iff, SparseCompletion.weighted_completion_rotated_cones_iff.

**Finset.max'**: SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_le_bound, SparseCompletion.residual_loss_bound_le, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.normalized_exact_weak_cover_maximum.

**Finset.sup'**: SparseCompletion.allocation_rounding_value_bound, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.exploitability_bounded_above, SparseCompletion.exploitability_continuous, SparseCompletion.exploitability_le_iff, SparseCompletion.exploitability_nonnegative, SparseCompletion.exploitability_perturbation, SparseCompletion.exploitability_strategy_distance, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.normalized_exact_weak_cover_maximum, SparseCompletion.normalized_weak_cover_maximum, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound, SparseCompletion.residual_loss_bound_le, SparseCompletion.residual_loss_bound_le_iff, SparseCompletion.residual_loss_bound_nonnegative, SparseCompletion.residual_loss_bound_ordered, SparseCompletion.residual_loss_bound_zero_iff, SparseCompletion.residual_loss_le_bound, SparseCompletion.response_le_exploitability, SparseCompletion.response_strategy_distance.

**Set.compl**: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

**Fintype.equivFin**: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

**Equiv.Set.sumCompl**: SparseCompletion.arbitrary_vertex_cover_sparse, SparseCompletion.arbitrary_vertex_cover_exact, SparseCompletion.arbitrary_vertex_subset_weak_sparse, SparseCompletion.arbitrary_vertex_subset_weak_exact, SparseCompletion.cover_equiv_anchor, SparseCompletion.cover_equiv_residual, SparseCompletion.cover_equiv_inverse_anchor, SparseCompletion.arbitrary_cover_free_residual, SparseCompletion.cover_relabel_on_residual, SparseCompletion.cover_relabel_on_anchor.

**LinearOrder**: SparseCompletion.residual_loss_bound_ordered, SparseCompletion.ordered_loss_values_nonempty, SparseCompletion.residual_loss_values_ordered, SparseCompletion.endpoint_bounds_from_order, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_value_ordered_interval_stability.

**InfSet**: SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

**ConditionallyCompleteLattice**: SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

**ConditionallyCompleteLinearOrder**: SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

**Set.prod**: SparseCompletion.exploitability_continuous, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_exploitability_continuous, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.fixed_game_value_le_witness, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_pairs_compact, SparseCompletion.gap_points_closed, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_le, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_le_witness, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

**Rat.castRec**: SparseCompletion.RationalBisection.value_certificate, SparseCompletion.RationalCertificate.accepted_full_game, SparseCompletion.RationalCertificate.check_iff_full_rows, SparseCompletion.RationalCertificate.realB_omitted, SparseCompletion.RationalCertificate.realB_stored, SparseCompletion.RationalCertificate.realQ_off, SparseCompletion.RationalCertificate.rows_iff, SparseCompletion.RationalCertificate.support_card_le.

**Set.Nonempty**: SparseCompletion.allocation_grid_nonempty, SparseCompletion.fixed_anchor_additive_value_enclosure, SparseCompletion.fixed_game_value_attained, SparseCompletion.fixed_game_value_bounds, SparseCompletion.floor_strategies_nonempty, SparseCompletion.gap_original_infimum_eq, SparseCompletion.gap_threshold_attained, SparseCompletion.gap_threshold_minimal_nonnegative, SparseCompletion.interval_matrices_nonempty, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.optimistic_support_value_attained, SparseCompletion.optimistic_support_value_ordered_stability, SparseCompletion.optimistic_support_value_stability, SparseCompletion.optimistic_value_attained, SparseCompletion.optimistic_value_interval_stability, SparseCompletion.optimistic_value_ordered_interval_stability, SparseCompletion.optimistic_value_projection_bound.

**Nat.floor**: SparseCompletion.allocation_grid_card, SparseCompletion.allocation_grid_nonempty, SparseCompletion.allocation_grid_strategies_compact, SparseCompletion.allocation_rounding_distance, SparseCompletion.allocation_rounding_in_grid, SparseCompletion.allocation_rounding_mass, SparseCompletion.allocation_rounding_preserves_floors, SparseCompletion.allocation_rounding_value_bound, SparseCompletion.optimistic_allocation_grid_bounds, SparseCompletion.removed_anchor_mass_bounds, SparseCompletion.rounded_allocation_finite_grid, SparseCompletion.rounded_anchor_bounds, SparseCompletion.rounded_anchor_grid_index.

**Monotone**: SparseCompletion.RationalBisection.excludes_below.


## Computable rational grid and supplied-point checking

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Nat/Sqrt/Basic.lean

Source SHA256 f57f88ba1daaa0db650ad5f2386681f17d2ee01bf33213581f2530946c829df6; Git blob e4048032b1086463ef16e44daee49df978ba5da3.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Nat/Sqrt/Basic.lean#L18-L36

```lean
/--
Integer square root function. Implemented via Newton's method.
-/
@[expose]
def sqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter n (1 <<< ((n.log2 / 2) + 1))
where
  /-- Auxiliary for `sqrt`. If `guess` is greater than the integer square root of `n`,
  returns the integer square root of `n`. -/
  iter (n guess : Nat) : Nat :=
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      iter n next
    else
      guess
  termination_by guess

end Nat

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Nat/Sqrt/Lemmas.lean

Source SHA256 e0527b1ac296129fc01678ef43aef51a170e31f728f1d5747cdb8092a3b6ecdb; Git blob 6e00a150b7f57fd2fd44aa28d648ab25c879be68.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Nat/Sqrt/Lemmas.lean#L97-L99

```lean
theorem sqrt_le (n : Nat) : sqrt n * sqrt n ≤ n := (sqrt_isSqrt n).left

theorem lt_succ_sqrt (n : Nat) : n < succ (sqrt n) * succ (sqrt n) := (sqrt_isSqrt n).right

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean

Source SHA256 30b77ea0918aa986f6617bef4ad99a8d79cd538a714c9f05134bcb6a5e490cc8; Git blob 9722e2373e6d49b7ec3e635a6125af895c9940b0.

```lean
/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L313-L318

```lean
/-- The floor of a rational number `a` is the largest integer less than or equal to `a`. -/
protected def floor (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Basic.lean#L277-L282

```lean
/-- Negation of rational numbers. -/
@[implicit_reducible]
protected def neg (a : Rat) : Rat :=
  { a with num := -a.num, reduced := by rw [Int.natAbs_neg]; exact a.reduced }

instance : Neg Rat := ⟨Rat.neg⟩

```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Lemmas.lean

Source SHA256 fb4134a5287f2ece513f686633599ecfcab42e78893fd32f3c9a721b1346b401; Git blob 200e880e1d859af402a800d560013dd45f30cb63.

```lean
/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Robin Arnez
-/
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Rat/Lemmas.lean#L1170-L1176

```lean
theorem le_floor_iff {x : Int} {a : Rat} : x ≤ a.floor ↔ (x : Rat) ≤ a := by
  constructor
  · intro h
    rw [← intCast_le_intCast] at h
    exact Rat.le_trans h (floor_le a)
  · intro h
    simpa using floor_monotone h

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Floor.lean

Source SHA256 e7ab2c6f3ed60c163295da29afc133d82041a8f1a7d50ecf65eda2a61a3617ac; Git blob 613f5decc4b6b5dcf3388b4fc73d2f72ac691a2e.

```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Rat/Floor.lean#L33-L50

```lean
namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/--
This variant of `floor_def` uses the `Int.floor` (for any `FloorRing`) rather than `Rat.floor`.
-/
protected theorem floor_def' {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

/--
This variant of `ceil_def` uses the `Int.ceil` (for any `FloorRing`) rather than `Rat.ceil`.
-/
protected theorem ceil_def' (q : ℚ) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean

Source SHA256 f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7; Git blob e38bd9356445865e98d15633af5bef1161b4f7df.

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L56-L71

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L120-L122

```lean
/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L171-L180

```lean
-/
class FloorRing (α) [Ring α] [LinearOrder α] where
  /-- `FloorRing.floor a` computes the greatest integer `z` such that `(z : α) ≤ a`. -/
  floor : α → ℤ
  /-- `FloorRing.ceil a` computes the least integer `z` such that `a ≤ (z : α)`. -/
  ceil : α → ℤ
  /-- `FloorRing.ceil` is the upper adjoint of the coercion `↑ : ℤ → α`. -/
  gc_coe_floor : GaloisConnection (↑) floor
  /-- `FloorRing.ceil` is the lower adjoint of the coercion `↑ : ℤ → α`. -/
  gc_ceil_coe : GaloisConnection ceil (↑)

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L190-L198

```lean
/-- A `FloorRing` constructor from the `floor` function alone. -/
@[instance_reducible]
def FloorRing.ofFloor (α) [Ring α] [LinearOrder α] [IsOrderedRing α] (floor : α → ℤ)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }


```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L341-L351

```lean

-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_lt.mpr (ha.trans_eq Int.cast_zero.symm)).le
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean

Source SHA256 1b0e45f02a914287979a2f39feb3f5b4808bff05f49e5a998e718168c4e36efb; Git blob 871c8ed11d3cd4edd89b375ef073edbab566229a.

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean#L177-L179

```lean
@[bound]
theorem le_ceil (a : R) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Sqrt.lean

Source SHA256 3ba3c0be75f7d9c912f8f74e24710d1ce771e692b79dd4cbb0dd6bf638ae1414; Git blob 6e0e55b225761cc0112e2b1c8d1d394ef867bfec.

```lean
/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Sqrt.lean#L29-L42

```lean

lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n

lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n

lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩

lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt


```

### Algorithm scope and literal routes

Nat.sqrt is the actual computable natural integer floor-square-root implemented by decreasing Newton iteration, not Real.sqrt or a classical existence choice. Core contracts give sqrt(n)^2<=n<(sqrt(n)+1)^2.

Nat.ceil on Rat selects FloorSemiring.ceil, through FloorRing.toFloorSemiring to Int.ceil(q).toNat. The actual Rat FloorRing is computably constructed by ofFloor using Rat.floor. ofFloor computes integer ceil as -Rat.floor(-q); it does not call the noncomputable Archimedean floorRing used for Real.

The primitive Rat.ceil is extensionally related but is not the literal selected instance path here. The evidence follows the actual -floor(-q) route and Nat truncation.

The chosen H=sqrt(ceil(Mr/eta))+1 is an admissible explicit integer grid. It is not asserted equal to canonical ceil(Real.sqrt(Mr/eta)); H=1 when r0 and parameters otherwise valid, and perfect-square ratios may have one additional node.

Rational grid nodes, calls and envelope are finite exact rational operations. Their equalities to the existing Real definitions are proved cast-coherence contracts. Definitions remain total on invalid parameters; interpolation/soundness require explicit M>0,r>=0,eta>0.

There is no runtime or bit-complexity theorem supplied by these contracts.

The separate size-bound module additionally proves H≤sqrt(Mr/η)+2 for M,r≥0,η>0. It remains a mathematical count bound, not a bit-cost theorem. The point checker checks a supplied rational q; it does not decide existential feasibility or construct rational B. Completed B is an actual existential Real matrix.

### Rational-grid affected declarations

**Fintype**: SparseCompletion.rational_anchor_response_real, SparseCompletion.rational_call_real, SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_check_iff, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_score_real.

**Finset**: SparseCompletion.rational_anchor_response_real, SparseCompletion.rational_call_real, SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_check_iff, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_score_real.

**Finset.prod**: SparseCompletion.rational_anchor_response_real, SparseCompletion.rational_call_real, SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_check_iff, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_score_real.

**Set.Icc**: SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**Nat.ceil**: SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_check_iff, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_grid_size_bound, SparseCompletion.rational_grid_size_linear_bound, SparseCompletion.rational_grid_size_positive, SparseCompletion.rational_grid_size_real_bound, SparseCompletion.rational_grid_size_sqrt_bound.

**FloorSemiring**: SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_check_iff, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_grid_size_bound, SparseCompletion.rational_grid_size_linear_bound, SparseCompletion.rational_grid_size_positive, SparseCompletion.rational_grid_size_real_bound, SparseCompletion.rational_grid_size_sqrt_bound.

**NNReal.sqrt**: SparseCompletion.rational_grid_size_sqrt_bound.

**Real.sqrt**: SparseCompletion.rational_grid_size_sqrt_bound.

**Real.toNNReal**: SparseCompletion.rational_grid_size_sqrt_bound.

**Convex**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**StarConvex**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**Finset.card**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**IsCompact**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**IsClosed**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**Continuous**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**LinearMap**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**ContinuousLinearMap**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**Set.image**: SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game.

**Rat.castRec**: SparseCompletion.rational_anchor_response_real, SparseCompletion.rational_call_real, SparseCompletion.rational_envelope_real, SparseCompletion.rational_finite_grid_implication, SparseCompletion.rational_gap_completed_witness, SparseCompletion.rational_gap_normalized_full_game, SparseCompletion.rational_grid_node_real, SparseCompletion.rational_grid_size_real_bound, SparseCompletion.rational_grid_size_sqrt_bound, SparseCompletion.rational_score_real.


### Exact rational grid size proof contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean

Source SHA256 1b0e45f02a914287979a2f39feb3f5b4808bff05f49e5a998e718168c4e36efb

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Semiring.lean#L357-L358

```lean
theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : R) < a + 1 :=
  lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

```


### Exact rational grid size proof contract

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Sqrt.lean

Source SHA256 3ba3c0be75f7d9c912f8f74e24710d1ce771e692b79dd4cbb0dd6bf638ae1414

```lean
/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Sqrt.lean#L29-L47

```lean

lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n

lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n

lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)

lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩

lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt

lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]

lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']

lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)

```
