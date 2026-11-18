# Material definitions in the four selected lower bounds

The comparison selects these theorem names.

- `BoundedEdgeRegularSubgraphs.theorem1_1_arbitrary`
- `BoundedEdgeRegularSubgraphs.theorem1_1_equalDegrees`
- `BoundedEdgeRegularSubgraphs.theorem1_1_lipschitz`
- `BoundedEdgeRegularSubgraphs.theorem1_1_lowRank`


The statement modules interpret the graph as a binary outcome under a finite
product probability law. The deterministic vertex degrees in the events sum
incident edge values. A complemented event describes the absence of a regular
induced set at the stated order or orders. The local predicates
`HasFloor`, `EqualExpectedDegrees`, `CubeLipschitz`, and
`HasRankCompletion` state the common probability interval, equality of row
sums, the first-variable maximum-norm condition, and the existence of a
symmetric bounded completion. The last predicate leaves diagonal entries free
within the stated interval. The slope condition on the cube uses all coordinate
inequalities through a nonnegative common tolerance.

The entries below record the pinned Mathlib definitions used in those
statements. `ChallengeSemantics` and `SolutionSemantics` check the same
probability, threshold, and rank interpretations through the two separate
entrypoints. The mathematical review assesses how these interpretations
correspond to the source paper.

## `MeasureTheory.Measure.pi`

The product law multiplies probabilities on cylinders indexed by the finitely many unordered edges. The construction passes through the product outer measure and the Caratheodory measurable sets. The cylinder identity is a proved characterization.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Constructions/Pi.lean)

SHA-256 `c42e64e87e9ca61e4e8a17e412ee339759f6ee453471618bcbfe098dc45da041`

```text
/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Constructions/Pi.lean#L210-L211).

```lean
protected irreducible_def pi : Measure (∀ i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Constructions/Pi.lean#L290-L293).

```lean
theorem pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi, pi'_pi]
```

## `ProbabilityTheory.bernoulliMeasure`

For distinct outcomes 1 and 0, the two masses are the given edge probability and its complement. Unit-interval weights scale the two Dirac measures. The pinned real-application lemma specifies their contributions on measurable sets.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Probability/Distributions/Bernoulli.lean)

SHA-256 `aa2ba1209900f522001849ee6aa715b86ad5e625b2d6f8f4cd8caf573e1c48eb`

```text
/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Probability/Distributions/Bernoulli.lean#L47-L48).

```lean
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Probability/Distributions/Bernoulli.lean#L76-L86).

```lean
lemma bernoulliMeasure_real_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    Ber(x, y, p).real s =
      if x ∈ s
        then if y ∈ s
          then (1 : ℝ)
          else toNNReal p
        else if y ∈ s
          then toNNReal (σ p)
          else 0 := by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]
```

## `MeasureTheory.Measure.real`

The conclusion compares the real-valued probability of a failure event to a real bound. The measure is evaluated in the extended nonnegative reals, then converted by toReal. Finite Bernoulli product probability laws give finite event masses.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean)

SHA-256 `9e7e2105e21cdb7dbe731515213bcd1f6cf78c902bcd2da7f33b468218d90664`

```text
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L102-L103).

```lean
protected def Measure.real {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) : ℝ :=
  (μ s).toReal
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L105-L106).

```lean
theorem measureReal_def {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.real s = (μ s).toReal := rfl
```

## `Set.Icc`

The probability and kernel-coordinate types use the closed interval including both endpoints. Membership expands to the conjunction of the lower and upper order inequalities. Subtype projection returns the real value.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean)

SHA-256 `53970116254a7e705eb85f92c9236be431966dbd61c1c1315a914a6d05e39b7b`

```text
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Set/Defs.lean#L76-L76).

```lean
def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }
```

## `Set.iUnion`

The graph event asserts the existence of an induced subset of the permitted order. The set supremum over the family has existential membership, indexed by finite vertex subsets satisfying the order predicate.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean)

SHA-256 `302c614100cbc978e2af66d21d5eb0e09eb39402e9ae52a166e6faaa36d3dc14`

```text
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean#L165-L166).

```lean
def iUnion (s : ι → Set α) : Set α :=
  iSup s
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean#L241-L243).

```lean
theorem mem_iUnion {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x ∈ _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
```

## `Set.preimage`

The induced regularity event pulls the local degree condition back to the ambient graph outcomes. A graph is in the preimage exactly when its restriction to edges of the given vertex set satisfies the local regularity condition.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean)

SHA-256 `60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e`

```text
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L135-L135).

```lean
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}
```

## `Set.compl`

The bounds are for the failure of the stated existence events. Complement membership expands to negated membership in the corresponding exact-order or at-least-order event.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean)

SHA-256 `4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7`

```text
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L249-L249).

```lean
protected def compl (s : Set α) : Set α := {a | a ∉ s}
```

## `Nat.ceil`

The logarithmic thresholds round up to a natural order. The FloorSemiring ceiling has the Galois connection with natural-number coercion. A natural order meets the ceiling exactly when its real value meets the unrounded threshold.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean)

SHA-256 `f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7`

```text
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L121-L122).

```lean
def ceil : α → ℕ :=
  FloorSemiring.ceil
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L148-L149).

```lean
theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
  gc_ceil_coe _ _
```

## `Finset.card`

The vertex order counts the elements of a finite subset. The finite set has an underlying duplicate-free multiset. Its multiset cardinality agrees with the usual count.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean)

SHA-256 `901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80`

```text
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L47-L48).

```lean
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## `Real.rpow`

The structural order thresholds and failure exponents use ordinary positive-base real powers. The definition takes the real part of a complex power. For a positive base, the checked contract identifies it with the exponential of the logarithm times the exponent.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean)

SHA-256 `5f4970fe329b14615ca6cfa3e0dcb0cf9d2017c98d2e3501237412aa2474e70b`

```text
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L35-L36).

```lean
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L51-L52).

```lean
theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), ite_eq_right (ne_of_gt hx)]
```

## `Real.log`

The thresholds in the arbitrary-array bounds use the natural logarithm. The positive-real branch is inverse to the real exponential. The ordinary square is a natural power of the logarithm.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)

SHA-256 `5c3ecb5112d5d46df46d3dff3efa1548095356259633b34885db8ab4275340a2`

```text
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L44-L45).

```lean
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L75-L76).

```lean
theorem log_exp (x : ℝ) : log (exp x) = x :=
  exp_injective <| exp_log (exp_pos x)
```

## `Real.exp`

The failure bounds use the usual natural exponential. The definition takes the real part of the complex exponential on the real axis. The complex exponential is defined by its convergent power series.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean)

SHA-256 `581fefd0139417fa56ef95b54103e415ae252d9d120f9da1cfe8039ff3d46bff`

```text
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean#L80-L81).

```lean
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
```

## `Real.sqrt`

The amplified logarithmic bound uses the nonnegative square root of the number of vertices. The definition applies NNReal.sqrt to the nonnegative part. The checked Real.sqrt_eq_rpow contract identifies the root with the one-half power.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean)

SHA-256 `f4e96c735ead60a8983bcf8eb6e38dfd05d8102c3f741094f73639858605bb6a`

```text
/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Real/Sqrt.lean#L112-L113).

```lean
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

## `Matrix.rank`

The rank cap is the rank of the real matrix that completes the edge array. The definition is the natural dimension of the range of the matrix-vector linear map. Over the real field with finite indices this is the usual column rank.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Rank.lean)

SHA-256 `4ce457849b67eca2d37842f1ebcac1dea88f16a202f5c6dfceb4bb6c6047e262`

```text
/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Rank.lean#L134-L135).

```lean
noncomputable def rank [CommSemiring R] (A : Matrix m n R) : ℕ :=
  finrank R <| LinearMap.range A.mulVecLin
```

## `Module.finrank`

Finite real vector-space dimension is a natural number. The definition uses the natural value of the cardinal-valued module rank. Subspaces of the finite-dimensional codomain in the completion hypothesis have finite rank.

[Upstream file](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean)

SHA-256 `4ab91c2b2e2d56f24c0260f25d55a31042cac8112a943a7c877594528c363e21`

```text
/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
```

Excerpt from [the pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L62-L63).

```lean
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)
```
