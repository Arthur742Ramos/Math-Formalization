# Material imported definitions at the exact Mathlib pin

The inventory records finite-index, interval, grid-size and finite-dimensional recombination meanings. Ordinary ordered-real algebra, logical connectives, casts and function application remain background infrastructure. No imported game-feasibility or sparse-completion target is assumed. Game predicates are fixed public definitions. Finset.sum is generated from the retained Finset.prod/to_additive source and checked by finite_sum_literal. Module.rank uses irreducible_def; its retained macro source and the actual finite-product dimension law are explicit rather than presenting it as a textual def.

Classical Caratheodory recombination is Mathlib work by Johan Commelin and Kim Morrison, part of the Sphere Eversion project. The finite-dimensional affine cardinal bound is upstream infrastructure. Our proof preserves all selected hinge values exactly, rather than formalizing the paper's inequality-based extreme-point argument. No novelty claim is made for recombination.

The repository checker authenticates supported definition entries and all retained file/excerpt bytes. Generated declarations and precise theorem contracts have their own retained source and compiled bridges. Independent review owns inventory completeness and semantics; source hashes alone do not prove either.

## Fintype

A finite type has a finite duplicate-free enumeration containing every element. Finite sums range over that enumeration. Empty types are allowed.

Affected selected declarations: SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff

## Finset

A finite set is a multiset with no duplicate entries. Membership, complement and subset sums refer to the finite indexing set, without multiplicities.

Affected selected declarations: SparseCompletion.skew_weighted_sum, SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.compactCompletion_skew, SparseCompletion.compactCompletion_bounds, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff

## Finset.prod

Multiplicative source for the generated additive Finset.sum definition. The to_additive attribute generates Finset.sum as the mapped underlying multiset sum; finite_sum_literal checks that exact value.

Affected selected declarations: SparseCompletion.skew_weighted_sum, SparseCompletion.response_guard, SparseCompletion.completion_cuts_necessary, SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.supported_response_zero, SparseCompletion.response_perturbation, SparseCompletion.compact_certificate_responses_iff, SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.block_response_bounds_iff, SparseCompletion.exact_score_bounds, SparseCompletion.exact_score_mean_zero, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate, SparseCompletion.compact_block_certificate_iff

## Set.Icc

The closed interval consists of x with a ≤ x and x ≤ b. The grid/envelope domain includes both endpoints; interval_literal unfolds the actual predicate.

Affected selected declarations: SparseCompletion.cuts_iff_call_bound, SparseCompletion.finite_grid_implication, SparseCompletion.canonical_grid_implication, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Nat.ceil

The natural ceiling delegates to FloorSemiring.ceil. FloorSemiring.gc_ceil says ceil a ≤ n iff a ≤ (n:ℝ); the natural ceiling is zero for negative a.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## FloorSemiring

Floor and ceiling operations with their natural-cast adjunction laws. The ceil field is a lower adjoint to the natural cast; natural_ceiling_meaning checks the resulting equivalence at ℝ.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## NNReal.sqrt

Nonnegative square root is the inverse order isomorphism of squaring on nonnegative reals. powOrderIso 2 supplies squaring; its inverse identities give a nonnegative root with square equal to the input.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Real.sqrt

The real square root applies NNReal.sqrt to Real.toNNReal. Negative inputs yield zero. Only nonnegative Mr/η is used; square_root_meaning proves the needed square and sign laws.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Real.toNNReal

Real-to-nonnegative-real conversion clips a real input below at zero. The underlying value is max r 0, with a proof of nonnegativity. For nonnegative inputs its coercion equals the original input.

Affected selected declarations: SparseCompletion.gridSize_bound, SparseCompletion.canonical_grid_implication, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Convex

Every point of the set is a star center of the set. Via StarConvex this means closure under nonnegative two-point real convex combinations; convex_literal proves the expanded quantifiers.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## StarConvex

All nonnegative combinations of a chosen center with a point of the set, with weights summing to one, remain in the set. Centers in the set quantify convexity. No topological closedness is assumed.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## convexHull

The closure operator generated by all convex supersets. Membership means belonging to every convex superset, proved by convex_hull_meaning. It is algebraic convex hull, not topological closure.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## AffineIndependent

Zero-sum finite affine relations with zero weighted subtraction have all coefficients zero. The point-subtraction base cancels when coefficient sum is zero. affine_independence_literal and weighted_subtraction_zero_sum audit the actual meaning.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Finset.weightedVSub

Finite weighted differences from a default affine base point. This is used only with zero total weight, where the base is arbitrary and cancels. The checked bridge specializes to vector-space base zero.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Finset.weightedVSubOfPoint

The linear map summing weights times differences from a specified base point. Its application is the literal finite sum; the zero-sum bridge verifies the needed base-zero interpretation.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## vectorSpan

The submodule spanned by all differences of two points in the set. vector_span_literal unfolds the pairwise-difference image; the dimension is at most that of the ambient feature space.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Submodule.span

The infimum of all submodules containing the supplied generating set. submodule_span_literal checks the precise intersection/infimum meaning; it is linear span, not an analytic closure.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Module.finrank

The natural-number conversion of the cardinal-valued module rank. Cardinal.toNat is zero on infinite cardinals. Here the feature space is a finite real product and the checked finite_feature_dimension law gives its actual finite dimension; no infinite-dimensional rank is interpreted as a support bound.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Finset.card

The number of elements in the underlying duplicate-free multiset. finite_card_literal checks this exact value. The support count is a count of original nonzero labels, not a count of distinct feature values.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Fintype.card

The cardinality of the finite universal enumeration. type_card_literal checks its link to Finset.card. Empty finite feature types are allowed, giving the mass-only one-point case.

Affected selected declarations: SparseCompletion.finite_moment_recombination, SparseCompletion.finite_feature_compression, SparseCompletion.sparse_cut_witness, SparseCompletion.exact_sparse_cut_witness, SparseCompletion.canonical_sparse_cut_witness, SparseCompletion.game_sparse_cut_certificate, SparseCompletion.exact_game_sparse_cut_certificate

## Mathlib/Data/Fintype/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean

Full-file SHA256: e69e8e7a3605d293a7ef6c4a7aaefde3191da4f33b43b7be09963eec2e44965c

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Defs.lean#L51-L62

Excerpt SHA256: ccc0167da005c12ce09e1e41af0a2ebbcda025a6f6d81a5ae5b97a10341ffd59

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

## Mathlib/Data/Finset/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean

Full-file SHA256: ac132a546c19ca9e9ec46f864faae346c2c613c8bd7123bb0807c4ad630c302d

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean#L72-L79

Excerpt SHA256: afb72753ded86e288bed4c75c35cefa870d2252544a7ba0146669917603c0134

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

## Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean

Full-file SHA256: e935efa96ad9381658f3158f900d04589c46d7e933cab15f4d8632e1af85527f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean#L59-L69

Excerpt SHA256: 26d8fa821bd539acece2d861933171554c86d441fbb32266ecc2ebc472639de1

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

## Mathlib/Order/Interval/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean

Full-file SHA256: 53970116254a7e705eb85f92c9236be431966dbd61c1c1315a914a6d05e39b7b

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L74-L81

Excerpt SHA256: cd66598cde677aa3908344faee474669a8c7c6e232e6e1a84b8e793e7e780439

```lean
/-- `Icc a b` is the left-closed right-closed interval $[a, b]$. -/
@[to_dual self (reorder := a b)]
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

to_dual_insert_cast Icc := by simp only [and_comm]

@[simp, grind =, push, to_dual none] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := .rfl
@[to_dual none] theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = Icc a b := rfl
```

## Mathlib/Algebra/Order/Floor/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean

Full-file SHA256: f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L115-L122

Excerpt SHA256: de25b129387a66cd093cc29cf122302dea76da950fa585813bfc65f682f479f7

```lean

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L57-L71

Excerpt SHA256: 5b0a713fe3d952383b08a08ac24046a02f7a047d4e22c7d21adaae9e36556b79

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

## Mathlib/Analysis/Real/Sqrt.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean

Full-file SHA256: f4e96c735ead60a8983bcf8eb6e38dfd05d8102c3f741094f73639858605bb6a

```lean
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L40-L51

Excerpt SHA256: 44755372bd21ff74f1a58cd2e570ae606fe486ff6d1f038944d034ad79420675

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L108-L113

Excerpt SHA256: 88f1e5e1bf15526c807ed9c89155d3b9b5de32dfba34833325412f2c81305a74

```lean

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

## Mathlib/Basic/NNReal/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean

Full-file SHA256: 5a94f78b3f6ce87106eea63ea8bfa48647de38cf2e51bff75f06a311ef821c99

```lean
/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L154-L159

Excerpt SHA256: 8161052c14e7de652bb8a2677551335ecb6ca8cce417d568327027c9c0c5724a

```lean
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)

theorem _root_.Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
```

## Mathlib/Analysis/Convex/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Basic.lean

Full-file SHA256: 9044a0be27a288e404cbd80670eb0e739271be1fdd7577dbf205dff40af24fcf

```lean
/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Basic.lean#L48-L54

Excerpt SHA256: 078a97ca6c626f88e61266b92f2efddb3e1c3ee4fa8ef852d10509ab034ffc39

```lean

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

```

## Mathlib/Analysis/Convex/Star.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Star.lean

Full-file SHA256: 7d8a7df5d59812e6d1bebdeb0cfddc109fb5a54b0973eff14c128af0ff933858

```lean
/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Star.lean#L70-L75

Excerpt SHA256: 7ecf378475156dd7f81e8604073d3181109ee9dec684fd126015a24617a8c029

```lean
/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

```

## Mathlib/Analysis/Convex/Hull.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Hull.lean

Full-file SHA256: 7f05ca2487110c7a2e35be41043231e1094e78e7dc34045202d4b0c85913e53b

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Hull.lean#L44-L62

Excerpt SHA256: 605899f186fb40f61e2c07a93a51e024978595102d39680d193ebf6f6789e2ec

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

## Mathlib/LinearAlgebra/AffineSpace/Independent.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Independent.lean

Full-file SHA256: 9475bae0945645d79cc089bb3eeee405e6fae6d6923c8f22e6686b3a53219594

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Independent.lean#L50-L61

Excerpt SHA256: 7f164359d0fa8376d2397dbda7bad305f7c4ca8a7c042825501ed381b6b873e2

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

## Mathlib/LinearAlgebra/AffineSpace/Combination.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean

Full-file SHA256: d7c58df194c17fb81cc55d9f20b4cd0aaef1b06695b434594e2c97b51c16f1a8

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean#L227-L249

Excerpt SHA256: fd94fabbae0c75716cc3bca470656c307b27f536aef93f1bc3d243a92237daf4

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/Combination.lean#L58-L68

Excerpt SHA256: 1bb5cb92f072372ce7b140d480299023b71dbf07d9efcaafa84777751219126b

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

## Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean

Full-file SHA256: db1a84f71e149014ac383885710a49afa0d625a144e776757fff81c1cc923981

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean#L62-L68

Excerpt SHA256: 272c10b93d49f1b1f4bb6b62f4fa415838dbcae098b88f7920631e98e9dd12b4

```lean
/-- The submodule spanning the differences of a (possibly empty) set of points. -/
def vectorSpan (s : Set P) : Submodule k V :=
  Submodule.span k (s -ᵥ s)

/-- The definition of `vectorSpan`, for rewriting. -/
theorem vectorSpan_def (s : Set P) : vectorSpan k s = Submodule.span k (s -ᵥ s) :=
  rfl
```

## Mathlib/LinearAlgebra/Span/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean

Full-file SHA256: a0403eb6f96f384672a7b52d7ddb94405d3d3b1c43f699facc3e99ef8b0c00c6

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Span/Defs.lean#L43-L48

Excerpt SHA256: 8464315a6e2c9c2bc34f4f9f8558933d9b3690e5d4cc006122167b8153070afc

```lean

variable (R) in
/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }

```

## Mathlib/LinearAlgebra/Dimension/Finrank.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean

Full-file SHA256: 4ab91c2b2e2d56f24c0260f25d55a31042cac8112a943a7c877594528c363e21

```lean
/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L54-L64

Excerpt SHA256: e10fb88fcac6bb07fb88d3b21991690f190df5504a12fc66b32f8cc5c9225766

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

## Mathlib/Data/Finset/Card.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean

Full-file SHA256: 901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L43-L53

Excerpt SHA256: 8c18fa0d55a08477b928d5955b55d36d561f651fa6b323ea9b52cb80e2127429

```lean

/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1

@[inherit_doc] scoped prefix:arg "#" => Finset.card

theorem card_def (s : Finset α) : #s = Multiset.card s.1 :=
  rfl
```

## Mathlib/Data/Fintype/Card.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean

Full-file SHA256: a77eb573a459ee525cfb4ac753dd05968ef2cc831d7549dc4e9036c7a90a1f00

```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Card.lean#L39-L43

Excerpt SHA256: 379822685f878466c61b39c9973dd913a967c72d08d98cae44625706b656097b

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
```

## Mathlib/Analysis/Convex/Caratheodory.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Caratheodory.lean

Full-file SHA256: 8e2ead25535366604c2caab3071e5549586f909fe70b885d1c75784e117720f2

```lean
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Caratheodory.lean#L148-L166

Excerpt SHA256: 533144aa86bb2dd19c680134a103822128c6cb8d60c2330f3637ebdaa4a45739

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

## Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean

Full-file SHA256: d1762f0257b80394b1d08f2cc68ad42c8723d5f6aefbcf7ce9e89a22a82eb864

```lean
/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean#L313-L321

Excerpt SHA256: cdad869f95b410165fa45789f6a2535cac0cd5a5159c4d67e562a2b71fd5a6dd

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

## Mathlib/LinearAlgebra/Dimension/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Basic.lean

Full-file SHA256: f1989e361485382c4a47a8712dbdd58a7c89b339788b7d75c0dac0d9a3a5f12f

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Basic.lean#L59-L72

Excerpt SHA256: cef3b2738e36b5276b058b94beb2d898174ec224db9fe06637064a37cd7cdc8c

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

## Mathlib/LinearAlgebra/Dimension/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Constructions.lean

Full-file SHA256: ba705b4a5e12709dfbd792ddd9946aafdcc276daf1a8778de760ec2f4e660363

```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Constructions.lean#L287-L293

Excerpt SHA256: c6f13ddd1919b5c8692290098ae29ca28b7e08a6f50c4cc777b04a88731d81ae

```lean

/-- The `finrank` of `(ι → R)` is `Fintype.card ι`. -/
theorem Module.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι → R) = Fintype.card ι := by
  simp [finrank]

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
```
