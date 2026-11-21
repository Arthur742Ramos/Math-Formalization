# Material imported definitions

The selected statements use finite graphs, finite algebra and limits at infinity. The table identifies the pinned upstream meanings and the selected contracts that use them. Both semantic test modules compile the concrete graph, threshold and arithmetic interpretations.

| Imported declaration | Meaning and dependency | Selected uses |
| --- | --- | --- |
| SimpleGraph | An undirected graph with symmetric, irreflexive adjacency. The vertex type Fin N fixes the host order. The set filter counts neighbors inside the chosen set. | InducedDegreeRepetition.degreeOn, InducedDegreeRepetition.LogScaleRepetition, InducedDegreeRepetition.Forces, InducedDegreeRepetition.OpenProblems.adj |
| SimpleGraph.induce | Restriction of both adjacency arguments to the subtype of selected vertices. Comap along the subtype embedding retains every internal edge. | InducedDegreeRepetition.degreeOn, InducedDegreeRepetition.degreeClass |
| SimpleGraph.degree | Number of neighbors in the induced graph. The finite neighbor set consists exactly of vertices adjacent to the chosen vertex. | InducedDegreeRepetition.degreeOn |
| Real.log | Natural logarithm on positive reals. Inverse of the real exponential there. The value at zero is zero and a finite initial segment has no effect on little-o. | InducedDegreeRepetition.LogScaleRepetition, InducedDegreeRepetition.SubexponentialThreshold, InducedDegreeRepetition.OpenProblems.BiasedRectangle, InducedDegreeRepetition.OpenProblems.AdjacencyApproximation, InducedDegreeRepetition.OpenProblems.ConditionalResidues |
| Real.exp | Real exponential, used for absolute sizes, probability rates and relative cut scales. Real part of the complex exponential on the real axis. | InducedDegreeRepetition.OpenProblems.DensityReduction, InducedDegreeRepetition.OpenProblems.Core, InducedDegreeRepetition.conditional_range |
| Nat.ceil | Least natural number above the real input. The ceiling adjunction yields the explicit inequality used to round the scale. | InducedDegreeRepetition.LogScaleRepetition, InducedDegreeRepetition.OpenProblems.RandomRestrictions |
| Asymptotics.IsLittleO | For every positive ε the magnitude of log g(k) is eventually bounded by ε times k. The constant in IsBigOWith is universally quantified before the eventual bound. | InducedDegreeRepetition.SubexponentialThreshold, InducedDegreeRepetition.subexponential_threshold |
| Filter.atTop | Filter of tails in the ordered index. Intersection of the principal filters of upper intervals. At natural or real indices, eventual membership has a single lower threshold. | InducedDegreeRepetition.SubexponentialThreshold, InducedDegreeRepetition.OpenProblems.ConditionalResidues, InducedDegreeRepetition.OpenProblems.DensityReduction |
| Filter.Eventually | A property holds for all sufficiently large indices. The set of satisfying indices belongs to the indicated filter, here atTop. | InducedDegreeRepetition.OpenProblems.DensityReduction, InducedDegreeRepetition.OpenProblems.RandomRestrictions, InducedDegreeRepetition.OpenProblems.AdjacencyApproximation, InducedDegreeRepetition.OpenProblems.ConditionalResidues |
| Filter.Tendsto | The dyadic rate divided by log(2^j+1) eventually exceeds each fixed real bound. The image filter lies below atTop. Both ordered tails appear in the proved threshold characterization. | InducedDegreeRepetition.OpenProblems.ConditionalResidues |
| Disjoint | Two finite sets share no member. The only common lower bound of their subsets is empty. | InducedDegreeRepetition.OpenProblems.CutBounds, InducedDegreeRepetition.OpenProblems.AdjacencyApproximation, InducedDegreeRepetition.integer_totals, InducedDegreeRepetition.OpenProblems.Positional |
| Nat.Prime | A prime natural has size at least two and no proper divisor above one. The definition uses irreducibility. Its positive-divisor characterization is a theorem. | InducedDegreeRepetition.TestModulus |
| Nat.ModEq | The two counts have equal remainders modulo q. The conclusion negates this relation. Remainder equality on natural numbers. | InducedDegreeRepetition.OpenProblems.ConditionalResidues |
| IsSquare | The additive declaration Even z is generated from IsSquare by to_additive. It means z = x + x for an integer x. Parity is evaluated on the signed difference, including negative differences. | InducedDegreeRepetition.integer_totals, InducedDegreeRepetition.OpenProblems.Adjustable |
| ZMod | Integers modulo a positive q, including composite q. Its carrier for q = n+1 is Fin (n+1), with modular addition and multiplication. | InducedDegreeRepetition.OpenProblems.BiasedRectangle, InducedDegreeRepetition.OpenProblems.adjMod, InducedDegreeRepetition.OpenProblems.HeavyRestriction |
| dotProduct | Sum of the coordinatewise products over the finite index set, computed modulo q. The vector dimension bounds the number of summands. | InducedDegreeRepetition.OpenProblems.BiasedRectangle |
| ZMod.stdAddChar | Additive character sending the residue of z to exp(2πiz/q). The circle-valued character is composed with the map to the complex numbers. | InducedDegreeRepetition.OpenProblems.BiasedRectangle |
| Matrix.mulVecLin | Linear map acting by matrix-vector multiplication. Its additive image controls complexity for composite moduli through cardinality. | InducedDegreeRepetition.OpenProblems.AdjacencyApproximation |
| AddMonoidHom.range | Image subgroup of the underlying additive map. The to_additive declaration has carrier equal to the set of values on all input vectors. | InducedDegreeRepetition.OpenProblems.AdjacencyApproximation |
| AddSubgroup | Additively closed subgroup containing zero and closed under negation. Membership of x−z in H specifies a translated coset. The carrier and closure under addition and zero are inherited from the additive submonoid. | InducedDegreeRepetition.coset_concentration, InducedDegreeRepetition.OpenProblems.HeavyRestriction |
| Nat.card | Natural cardinality of the subgroup or image, finite in every use here. Cardinal.toNat agrees with Fintype.card on finite enumerated types. | InducedDegreeRepetition.coset_concentration, InducedDegreeRepetition.OpenProblems.HeavyRestriction, InducedDegreeRepetition.OpenProblems.AdjacencyApproximation |
| Fintype.piFinset | All indexed choices from the coordinate pools, with order and repetitions. A function belongs exactly when every coordinate belongs to its assigned set. | InducedDegreeRepetition.OpenProblems.RandomRestrictions, InducedDegreeRepetition.OpenProblems.SimultaneousAdjustment |
| InfSet | The natural-number infimum is the least member of a nonempty set. The forcing set is nonempty by the Ramsey bound. The Nat instance uses Nat.find on a nonempty set and zero on the empty set. Membership and the universal lower bound prove leastness. | InducedDegreeRepetition.threshold, InducedDegreeRepetition.SubexponentialThreshold |
| Finset.max' | On a nonempty set the maximum belongs to the set and bounds every member from above. The generated order dual Finset.min' gives the minimum and the reverse bound. Both extrema are suprema in the corresponding order. The project's low and high return zero on the empty set. Lemma 10 assumes nonempty allowed sets. | InducedDegreeRepetition.low, InducedDegreeRepetition.high, InducedDegreeRepetition.integer_totals |
| Finset.Icc | The finite integer interval includes both endpoints. The locally finite order supplies the interval enumeration and its membership theorem. | InducedDegreeRepetition.integer_totals |
| Complex.instNorm | Complex modulus of the unnormalized sum over all ordered label pairs. It is the nonnegative square root of normSq; the rectangle hypothesis supplies the normalization as the real lower bound a*b/4. | InducedDegreeRepetition.OpenProblems.BiasedRectangle |
| AddMonoid | Multiplication by q counts repeated addition in the group; annihilation means q copies sum to zero for every element. The zero and successor fields specify this operation for all natural q. The theorem allows composite q. | InducedDegreeRepetition.coset_concentration |
| Finset.card | Cardinality counts each element of a finite set once. Distinct ordered tuples are distinct elements of the sample space. Cardinality of the underlying nodup multiset. | InducedDegreeRepetition.degreeClass, InducedDegreeRepetition.OpenProblems.RandomRestrictions |
| Finset.filter | Filters the indicated finite population by a predicate. Membership requires both membership in the original set and satisfaction of the predicate. | InducedDegreeRepetition.degreeClass, InducedDegreeRepetition.degreeOn, InducedDegreeRepetition.OpenProblems.HeavyRestriction |

## Mathlib/Combinatorics/SimpleGraph/Basic.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Basic.lean
SHA-256 97f49ff9b52fe1906b6a2071422b35ec496cd6b3d9d81043e77e56efceb0a73f
```lean
/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L95-L99
Excerpt SHA-256 5a0f97b61920c3141b820a5415169f9945deb85b92649e1b0099fca3f44f7cf3
```lean
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## Mathlib/Combinatorics/SimpleGraph/Maps.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Maps.lean
SHA-256 1cbcdb71178ac50a3be430a614c058db6eb993ab3c7925d6596b55101b6fdb37
```lean
/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Maps.lean#L225-L228
Excerpt SHA-256 2673b213c55122bc828a19dfe55d742a081d78aca7615be34eb5c2662166b078
```lean
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Maps.lean#L230-L231
Excerpt SHA-256 dda7473a948a75b07ff8b1913fde1ed796f5b113878f8a8b8bb6d4c3b7e2ecf8
```lean
variable {G} in
lemma induce_adj {s : Set V} {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v := .rfl
```

## Mathlib/Combinatorics/SimpleGraph/Finite.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Finite.lean
SHA-256 0517648009f90f3488fc3058d93fe8d40d9bea984f5686d68f77ecf78b9546f0
```lean
/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L241-L242
Excerpt SHA-256 d2064573034e7eb742578a174d1c66084709df0e22f3cadb50cf33a8348579ab
```lean
/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L169-L170
Excerpt SHA-256 09247e6c27f4077aa1fa6bb8436268395bdb69b331ace0a478e627fc3ce1d6e6
```lean
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L180-L181
Excerpt SHA-256 5ae571efa8399260acc357b20eb50d98a7f6c636616155b295aed926952d82e2
```lean
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset
```

## Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
SHA-256 5c3ecb5112d5d46df46d3dff3efa1548095356259633b34885db8ab4275340a2
```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L39-L45
Excerpt SHA-256 ed8405cfafce777b874a51babc3d28fb29f29ee75915a9d2a37051300c2d412d
```lean
/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot, wikidata Q11197]
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean#L59-L61
Excerpt SHA-256 9880153243328593103c34290f9aee7a1127a984c169c20cb3ce840f3cc4b92a
```lean
theorem exp_log (hx : 0 < x) : exp (log x) = x := by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx
```

## Mathlib/Analysis/Complex/Exponential.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean
SHA-256 581fefd0139417fa56ef95b54103e415ae252d9d120f9da1cfe8039ff3d46bff
```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Exponential.lean#L78-L81
Excerpt SHA-256 a7385651b357da90d61967089970c8f34d99805fea443abe98f23d73a1ae76d3
```lean
/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot, wikidata Q168698]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
```

## Mathlib/Algebra/Order/Floor/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean
SHA-256 f6cc4cbab72e40e7afadb67d625a720359c26b32b9293a72255df2018a7876f7
```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L120-L122
Excerpt SHA-256 4cd52aacc3214c6d11175a1aa30a52d59c7f644443637f07ec0db5661c165dc0
```lean
/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Order/Floor/Defs.lean#L148-L149
Excerpt SHA-256 8ae41cb8d7f2ea73fde8e8fb56a2bae687124445b139a70549d8f1fd6a3fdb0c
```lean
theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
  gc_ceil_coe _ _
```

## Mathlib/Analysis/Asymptotics/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean
SHA-256 68ef9c1b2d13f99770bcd0c679a23f078f634ea344ff914d7d634ba1682104ed
```lean
/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean#L169-L170
Excerpt SHA-256 720fde86dc6c7d8783715be44be10a80d5f50d4a971a041acdfe53d2075335c3
```lean
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean#L73-L74
Excerpt SHA-256 0ad02c41d905266ca6cdfc7962adc06d76d44a9bc7d64cf1f3a56b7f5ff576b7
```lean
irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Asymptotics/Defs.lean#L182-L183
Excerpt SHA-256 9736d24790d06610f12dded26187fb09451932388d3ea3407a6b4d5e52052cf2
```lean
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]
```

## Mathlib/Order/Filter/AtTopBot/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean
SHA-256 4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621
```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L39-L40
Excerpt SHA-256 d3328cf87e867b693da5613f3f5df4b1b898af75356721aec5df7b9fec3ff3b3
```lean
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
```

## Mathlib/Order/Filter/AtTopBot/Basic.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Basic.lean
SHA-256 6320c2e81caeea51c7a80593bea9723294e20acf2355d9a747685de6ba637b96
```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Basic.lean#L79-L79
Excerpt SHA-256 27cf8a92f031539196660d31a1ac7bca28550a1837a14ef16935bf6e54e573c1
```lean
lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b := mem_atTop_sets
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Basic.lean#L185-L186
Excerpt SHA-256 20fd1d66873448f42d85a9d9d5f5e26bf734fc52b8fc74daf782a72df39211c3
```lean
theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
  tendsto_iInf.trans <| forall_congr' fun _ => tendsto_atTop_principal
```

## Mathlib/Order/Filter/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean
SHA-256 d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5
```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L278-L282
Excerpt SHA-256 efd1b93fe352a77989c58c47fb69efa671f03a22f6dbc2b8f022b1a6194aae9c
```lean

/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L422-L423
Excerpt SHA-256 e67e1ffbfd08c931795585daf560352d7def861a308f3faf48bcd4cbbd2267e2
```lean
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
```

## Mathlib/Order/Disjoint.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean
SHA-256 5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c
```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L48-L49
Excerpt SHA-256 0afa2cf8eba8be7e8c79707dafde25b73970201e3d74bd9888afabf992c96ba2
```lean
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```

## Mathlib/Data/Finset/Disjoint.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Disjoint.lean
SHA-256 c8e070e0329aa6b0272013c6f89bc010ed6dd94ca18810837e7916688ad45bc0
```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Disjoint.lean#L47-L50
Excerpt SHA-256 2870c6131e4a630aa7b28e987de68135b4488c09735284026820e89879b41982
```lean
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => notMem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩
```

## Mathlib/Data/Nat/Prime/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Prime/Defs.lean
SHA-256 aebd695f444b13ff056ba32c43c88d31b327a5e65d2a3e0ed4784643c542a59c
```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Prime/Defs.lean#L42-L43
Excerpt SHA-256 2088233bb327cca0347feb1e0d8acbed990f096187c7178b009e8c4592105a64
```lean
def Prime (p : ℕ) :=
  Irreducible p
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/Prime/Defs.lean#L107-L112
Excerpt SHA-256 f0b595506e1d8a27638f68ff0f488331036c588b31646065f2edaa5ea0b23db2
```lean
theorem prime_def_lt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
  prime_def.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩
```

## Mathlib/Data/Nat/ModEq.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/ModEq.lean
SHA-256 a497c26a9c0ceab9ce37458de4dcb3a1647ef67121e74a2683ec33c6b3bebd1e
```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Nat/ModEq.lean#L35-L37
Excerpt SHA-256 b16b7194a9a24e6044b4a92a17f30d9ec07cef07cab500ffd555a0a7d99d9b7f
```lean
/-- Modular equality. `n.ModEq a b`, or `a ≡ b [MOD n]`, means that `a % n = b % n`. -/
def Nat.ModEq (n a b : ℕ) :=
  a % n = b % n
```

## Mathlib/Algebra/Group/Even.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Even.lean
SHA-256 1180fa9ac282e55257e95c8402acd7314fcbd0a18bcfdede92a3cde16e1db630
```lean
/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Even.lean#L53-L57
Excerpt SHA-256 7125531ddf4279b54d67e69b7c19775a64b46d535224b572093f698534ace65d
```lean
/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some root `r : α`. -/
@[to_additive /-- An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
for some `r : α`. -/]
def IsSquare (a : α) : Prop := ∃ r, a = r * r
```

## Mathlib/Data/ZMod/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/ZMod/Defs.lean
SHA-256 7090954d33f43bdcbe26e02eb5b10c52a5f0895dbe7009806a88fe4704bc2ce4
```lean
/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/ZMod/Defs.lean#L139-L141
Excerpt SHA-256 ce676ac97ed1d852f11e74117c8c30873b0e2ec6ae29e6e0f42d5a95a1def359
```lean
def ZMod : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)
```

## Mathlib/Data/Matrix/Mul.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Matrix/Mul.lean
SHA-256 389814a6174e73b69048066a00d5f6429812c62d40b0da09086ca6b3ac2b6f66
```lean
/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Matrix/Mul.lean#L72-L73
Excerpt SHA-256 845ac48216569b548ccb957fafad6c1307bea4e8024a0bb3aa0eb65f6207e854
```lean
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
```

## Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean
SHA-256 ee1e323e0d276bb12f0614141a7f650365c25b787683baa71cb19a7ec898d18e
```lean
/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L82-L83
Excerpt SHA-256 3feb77180fcd210b5c1763c2d14a4edb18f1530a7b2f21f2d6f5696b4b691026
```lean
/-- The additive character from `ZMod N` to `ℂ`, sending `j mod N` to `exp (2 * π * I * j / N)`. -/
noncomputable def stdAddChar : AddChar (ZMod N) ℂ := Circle.coeHom.compAddChar toCircle
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L86-L87
Excerpt SHA-256 4e2f349d75b44cf9bceb2be115a15666b596d23d92cd1546c7c2ab37c5cb7db2
```lean
lemma stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]
```

## Mathlib/LinearAlgebra/Matrix/ToLin.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/ToLin.lean
SHA-256 9aefbf5b4504a069dd6ad05d5a1c8e5a0d7ba9ca5ff9317f360b25cee806b1cd
```lean
/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L286-L286
Excerpt SHA-256 2dabb57f5491963cf61b0d164b098502d609aa01c1c228672939ef4e76303787
```lean
abbrev Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R := mulVecBilin R R M
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L292-L294
Excerpt SHA-256 c23537a103010a5b7fda17926575e71c42b669ef25e087e276f513b5ecee21ae
```lean
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M *ᵥ v :=
  rfl
```

## Mathlib/Algebra/Group/Subgroup/Ker.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Ker.lean
SHA-256 04358e0780c6a3d533a13fd75d54af04278af17735a512ca13f59ca25e910141
```lean
/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Ker.lean#L63-L67
Excerpt SHA-256 362a445a435a9f50494f2ce4672a32e4e9f7b06e2b8f7e3ce3ab1c2e74e4c95f
```lean

/-- The range of a monoid homomorphism from a group is a subgroup. -/
@[to_additive /-- The range of an `AddMonoidHom` from an `AddGroup` is an `AddSubgroup`. -/]
def range (f : G →* N) : Subgroup N :=
  Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Ker.lean#L77-L79
Excerpt SHA-256 91a6bf75bc549033b6c4d49f2d0c911a5db03951173519f8a1ce7439c804a42d
```lean
@[to_additive (attr := simp)]
theorem mem_range {f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl
```

## Mathlib/Algebra/Group/Subgroup/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Defs.lean
SHA-256 552903abcab0523f0c6571210b6f3a00e51604402cfe11b2b13deb45eafa3662
```lean
/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Subgroup/Defs.lean#L303-L305
Excerpt SHA-256 ae0ebf3bdb10d0e691a873ec73d9faafe25df7c0f1583a9a4a7d548fb510f1e4
```lean
structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x ∈ carrier → -x ∈ carrier
```

## Mathlib/SetTheory/Cardinal/Finite.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/SetTheory/Cardinal/Finite.lean
SHA-256 d0bb8f1f00469a940dcc8ca404a9d4f7157516c40a4d6aa0fbbc622e50c42e94
```lean
/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/SetTheory/Cardinal/Finite.lean#L39-L42
Excerpt SHA-256 78e8d3968bcd66799d38f9bf52d2bd94ca6da1a3751ce0f569902c14c86337d8
```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/SetTheory/Cardinal/Finite.lean#L45-L46
Excerpt SHA-256 2315ea68715fae72322575ad3a834e383206a7daf1b5ae85e2b31078c5538670
```lean
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card
```

## Mathlib/Data/Fintype/Pi.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean
SHA-256 3621d016ef00906a9538347e3565bc44f5fe22210006ba64009b183c8ff6338f
```lean
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean#L32-L34
Excerpt SHA-256 ab4677f949d36a983103e3ea90e285dc49c6f2a0a696c96dbda017cbf183a3f8
```lean
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Fintype/Pi.lean#L37-L45
Excerpt SHA-256 7dfb3a2f8455e91480e626f4999eb88d02a2e263f1e6242b8e38694f44d2fb0f
```lean
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

## Mathlib/Order/SetNotation.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean
SHA-256 302c614100cbc978e2af66d21d5eb0e09eb39402e9ae52a166e6faaa36d3dc14
```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/SetNotation.lean#L50-L52
Excerpt SHA-256 19fd07c33a23b5959fe476cd6a9ebcbbe771bd612548feef715fc5f4205a73ed
```lean
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α
```

## Mathlib/Order/Lattice/Nat.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice/Nat.lean
SHA-256 1e3a5f2ff1efa38926bfafb88d168b1495a5b01c6fd77e83efaf401eff26f6ed
```lean
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice/Nat.lean#L28-L30
Excerpt SHA-256 b73f2a9e87a4b68b825e2c53498820f26d3b509b727562289aefd9d7ef066089
```lean
open scoped Classical in
noncomputable instance : InfSet ℕ :=
  ⟨fun s ↦ if h : ∃ n, n ∈ s then @Nat.find (fun n ↦ n ∈ s) _ h else 0⟩
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice/Nat.lean#L75-L78
Excerpt SHA-256 4b34b7f351a76ca1713469ae018cd838efd62fcecff7b51635095e31b6c95c5b
```lean
theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Lattice/Nat.lean#L86-L89
Excerpt SHA-256 70e01876cfbeaa96c56007ef549b553050e317a8ac9f6d283f45e1fecb04f8ed
```lean
protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  classical
  rw [Nat.sInf_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm
```

## Mathlib/Data/Finset/Max.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean
SHA-256 f9381a30f98377e15faa35c02d19d3fa0d6576c1709460ed699f4616e4d2539e
```lean
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L128-L136
Excerpt SHA-256 b3e47a2484cd671db9f34d2a7726eebc61fda30e1251e8d06026c30059225b8e
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
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Max.lean#L140-L146
Excerpt SHA-256 4c1162b041754029e1092db0e81bb257c21c1d6ff8542afe07b62f21be20a225
```lean
@[to_dual]
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

@[to_dual min'_le]
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
```

## Mathlib/Order/Interval/Finset/Defs.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean
SHA-256 023c4216dc4c48cc0a97e5ceb876aa54e1db126b19097ee89c4d3b12059970a8
```lean
/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean#L280-L281
Excerpt SHA-256 bf0fe201275761cee2973e0eef9c5ba5c276aebfb44219f6c2dfa4c211f3c6bd
```lean
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Interval/Finset/Defs.lean#L301-L302
Excerpt SHA-256 2d345b70ec57c48d0dd2f67df91df71f7e302055e32554a1281a0aa21696c970
```lean
theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
  LocallyFiniteOrder.finset_mem_Icc a b x
```

## Mathlib/Analysis/Complex/Norm.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean
SHA-256 7f719d7b3ba3ba8b4667a8f79e7efd5d8fb4da2b82dcca011e64129113a63eba
```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean#L28-L29
Excerpt SHA-256 d6a35e79c8010638732e56adf66069c78b71f7b8e63a019fd601d4298c1afe3d
```lean
instance instNorm : Norm ℂ where
  norm z := √(normSq z)
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean#L31-L31
Excerpt SHA-256 94d132dbaf093131c130172af15de2182ed0db7d65a678977a27b141a940432b
```lean
theorem norm_def (z : ℂ) : ‖z‖ = √(normSq z) := (rfl)
```

## Mathlib/Algebra/Group/Monoid.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Monoid.lean
SHA-256 192a415f3decda0c5c21f8c6c04bdc26fd7072cb47ded0b0d0aa2ba09e204c35
```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Group/Monoid.lean#L379-L383
Excerpt SHA-256 646de24dc2f21a72eef635ad527574ee04c75cb10148b23afd8f070869f6dd2d
```lean
class AddMonoid (M : Type*) extends Zero M, Add M, AddSemigroup M, AddZeroClass M, NSMul M where
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero (x : M) : 0 • x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ (n : ℕ) (x : M) : (n + 1) • x = n • x + x := by intros; rfl
```

## Mathlib/Data/Finset/Card.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean
SHA-256 901b74774650c909674c06dc8a78882db528af0b296cede9ef7b716079665e80
```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Card.lean#L47-L48
Excerpt SHA-256 7341a0826770c82cb78620546f7050992224ded33b925f12044106a8a8bcac5b
```lean
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Mathlib/Data/Finset/Filter.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Filter.lean
SHA-256 7e79aa65a47a4552534e7042f18751f575cc4ba2b4252ac2fb4fa65d88369c2d
```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Filter.lean#L52-L53
Excerpt SHA-256 c5a516ba51ad0a5cc3937f269400a85c8f265463ce67ae75107a57e118f3beda
```lean
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Filter.lean#L127-L128
Excerpt SHA-256 86654e74ef8024a0879abd34144c2d49706aa6cbe6a77f736219090bbe86f9db
```lean
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Multiset.mem_filter
```

## Counting ordered tuple positions in Lean core

`InducedDegreeRepetition.tupleDegree` uses `List.countP`. Each matching position increments the accumulator, including repeated occurrences of the same vertex. The nil and cons equations establish this interpretation by induction. Both entrypoint tests apply the cons equation to the project definition. The Lean release identifies core commit `11acb17ec6b07a8f9e9173e6845197929540936b`.

[Upstream source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/List/Basic.lean#L1796-L1800)

File SHA-256 `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293`. Excerpt SHA-256 `1369b68756eed48e6bc8963d22d1853554576f5b476d8683e754aa793399a75d`.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
@[inline] def countP (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `countP`: `countP.go p l acc = countP p l + acc`. -/
  @[specialize] go : List α → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => if p x then go xs (acc + 1) else go xs acc
```

[Upstream source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/List/Count.lean#L58-L59)

File SHA-256 `4cf663e7844728b7762b9421fedfe044d33ff3a89ccc7e6f4bfd213c6ab336b6`. Excerpt SHA-256 `3afe7cb9cc910ca363b285b20a5945f99e190170b1f3498f599e34b46d3bbe73`.

```lean
/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
theorem countP_cons {a : α} {l : List α} : countP p (a :: l) = countP p l + if p a then 1 else 0 := by
  by_cases h : p a <;> simp [h]
```
