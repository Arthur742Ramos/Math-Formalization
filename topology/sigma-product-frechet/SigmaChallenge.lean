/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
Substantive proof and packaging contributions: OpenAI Codex.
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order

/-!
# Sequential convergence in countable-support Σ-products

The topology is induced by the ordinary product topology. Support is measured
relative to an explicit basepoint; finite supports are not substituted for
countable supports. The sequence construction schedules coordinates from the
target and every previously selected point.
-/

public section

open Set Filter Topology Function

universe u v

namespace SigmaFrechet

variable {ι : Type u} {X : ι → Type v}

/-- Coordinates on which a point differs from the chosen basepoint. -/
@[expose] def deviationSupport (b x : ∀ i, X i) : Set ι := {i | x i ≠ b i}

/-- The countable-support Σ-product, with the canonical subtype topology. -/
abbrev SigmaProduct (b : ∀ i, X i) :=
  {x : ∀ i, X i // (deviationSupport b x).Countable}

variable [∀ i, TopologicalSpace (X i)]

/-- Every closure point in a Σ-product of first-countable factors is approached
by a sequence from the set. No separation or countability of the index is assumed. -/
theorem exists_sequence (b : ∀ i, X i) [∀ i, FirstCountableTopology (X i)]
    {s : Set (SigmaProduct b)} {x : SigmaProduct b} (hx : x ∈ closure s) :
    ∃ a : ℕ → SigmaProduct b, (∀ n, a n ∈ s) ∧ Tendsto a atTop (𝓝 x) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    obtain ⟨y, _, hy⟩ := mem_closure_iff_nhds.mp hx univ univ_mem
    refine ⟨fun _ => y, fun _ => hy, ?_⟩
    have hxy : y = x := Subsingleton.elim _ _
    simpa only [hxy] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
  | inr hι =>
    let enum (z : SigmaProduct b) : ℕ → ι :=
      enumerateCountable z.property (Classical.arbitrary ι)
    have covers (z : SigmaProduct b) {i : ι} (hi : z.val i ≠ b i) :
        ∃ k, enum z k = i := subset_range_enumerate z.property _ hi
    choose U hU using fun i => (𝓝 (x.val i)).exists_antitone_basis
    let F (n : ℕ) (prev : Fin n → SigmaProduct b) : Finset ι :=
      (Finset.range (n + 1)).image (enum x) ∪
        Finset.univ.biUnion (fun m : Fin n =>
          (Finset.range (n + 1)).image (enum (prev m)))
    have pick (n : ℕ) (prev : Fin n → SigmaProduct b) :
        ∃ y : SigmaProduct b, y ∈ s ∧ ∀ i ∈ F n prev, y.val i ∈ U i n := by
      let t : Set (SigmaProduct b) := ⋂ i ∈ F n prev, {y | y.val i ∈ U i n}
      have ht : t ∈ 𝓝 x := by
        apply (biInter_finset_mem _).2
        intro i _
        exact ((continuous_apply i).comp continuous_subtype_val).continuousAt.preimage_mem_nhds
          ((hU i).toHasBasis.mem_of_mem trivial)
      obtain ⟨y, hyt, hys⟩ := mem_closure_iff_nhds.mp hx t ht
      refine ⟨y, hys, ?_⟩
      simpa only [t, mem_iInter, mem_ofPred_eq] using hyt
    choose q hq using pick
    let a : ℕ → SigmaProduct b :=
      Nat.strongRec fun n prev => q n (fun m => prev m.val m.isLt)
    have an (n : ℕ) : a n = q n (fun m : Fin n => a m.val) := by
      dsimp only [a]
      rw [Nat.strongRec_eq]
    have ha (n : ℕ) : a n ∈ s ∧
        ∀ i ∈ F n (fun m : Fin n => a m.val), (a n).val i ∈ U i n := by
      rw [an]
      exact hq n _
    refine ⟨a, fun n => (ha n).1, tendsto_subtype_rng.2 (tendsto_pi_nhds.2 ?_)⟩
    intro i
    by_cases hi : x.val i ≠ b i
    · obtain ⟨k, hk⟩ := covers x hi
      apply (hU i).toHasBasis.tendsto_right_iff.2
      intro l _
      filter_upwards [eventually_ge_atTop (max k l)] with n hn
      apply (hU i).antitone (le_trans (le_max_right k l) hn)
      apply (ha n).2 i
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩
    · by_cases hai : ∃ m, (a m).val i ≠ b i
      · obtain ⟨m, hm⟩ := hai
        obtain ⟨k, hk⟩ := covers (a m) hm
        apply (hU i).toHasBasis.tendsto_right_iff.2
        intro l _
        filter_upwards [eventually_ge_atTop (max (m + 1) (max k l))] with n hn
        apply (hU i).antitone (show l ≤ n by omega)
        apply (ha n).2 i
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨⟨m, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩
      · push Not at hai
        have heq : (fun n => (a n).val i) = fun _ : ℕ => x.val i := by
          funext n
          exact (hai n).trans (not_ne_iff.mp hi).symm
        rw [heq]
        exact tendsto_const_nhds

/-- Countable-support Σ-products of first-countable spaces are Fréchet–Urysohn. -/
theorem frechetUrysohnSpace (b : ∀ i, X i) [∀ i, FirstCountableTopology (X i)] :
    FrechetUrysohnSpace (SigmaProduct b) :=
  ⟨fun _ _ hx => exists_sequence b hx⟩

/-- A countable family of countably supported points has its entire closure in
one countable-coordinate section. Closed basepoint singletons are essential here. -/
theorem countable_closure_support (b : ∀ i, X i) [∀ i, T1Space (X i)]
    {s : Set (∀ i, X i)} (hs : s.Countable)
    (hsupp : ∀ y ∈ s, (deviationSupport b y).Countable) :
    ∃ J : Set ι, J.Countable ∧ ∀ x ∈ closure s, deviationSupport b x ⊆ J := by
  classical
  let J : Set ι := ⋃ y ∈ s, deviationSupport b y
  refine ⟨J, hs.biUnion hsupp, ?_⟩
  intro x hx i hi
  by_contra hij
  have hc : IsClosed {y : ∀ i, X i | y i = b i} :=
    isClosed_singleton.preimage (continuous_apply i)
  have hsub : s ⊆ {y : ∀ i, X i | y i = b i} := by
    intro y hy
    by_contra hne
    exact hij (mem_iUnion_of_mem y (mem_iUnion_of_mem hy hne))
  exact hi (closure_minimal hsub hc hx)

/-- Countably supported points are sequentially closed in an arbitrary product
of T₁ spaces, even when they are not topologically closed. -/
theorem isSeqClosed_countableSupport (b : ∀ i, X i) [∀ i, T1Space (X i)] :
    IsSeqClosed {x : ∀ i, X i | (deviationSupport b x).Countable} := by
  intro a x ha hx
  obtain ⟨J, hJ, hsub⟩ := countable_closure_support b (countable_range a)
    (by rintro _ ⟨n, rfl⟩; exact ha n)
  exact hJ.mono (hsub x (mem_closure_of_tendsto hx
    (Eventually.of_forall fun n => mem_range_self n)))

/-- The Σ-product has countable tightness, stated with an explicit countable
subset and closure witness rather than a new cardinal invariant. -/
theorem countable_tightness (b : ∀ i, X i) [∀ i, FirstCountableTopology (X i)]
    {s : Set (SigmaProduct b)} {x : SigmaProduct b} (hx : x ∈ closure s) :
    ∃ t : Set (SigmaProduct b), t.Countable ∧ t ⊆ s ∧ x ∈ closure t := by
  obtain ⟨a, ha, hax⟩ := exists_sequence b hx
  exact ⟨range a, countable_range a, by rintro _ ⟨n, rfl⟩; exact ha n,
    mem_closure_of_tendsto hax (Eventually.of_forall fun n => mem_range_self n)⟩

/-- Every topological subspace of the Σ-product is Fréchet–Urysohn. In particular,
this applies to compact subspaces of real Σ-products (Corson compacta). -/
theorem subspace_frechetUrysohnSpace (b : ∀ i, X i)
    [∀ i, FirstCountableTopology (X i)] (s : Set (SigmaProduct b)) :
    FrechetUrysohnSpace s := by
  let := frechetUrysohnSpace b
  infer_instance

/-- The countable-support Σ-product is dense in the whole ordinary product.
This assertion does not require first countability or separation. -/
theorem dense_countableSupport (b : ∀ i, X i) :
    Dense {x : ∀ i, X i | (deviationSupport b x).Countable} := by
  classical
  apply dense_iff_inter_open.mpr
  intro o ho hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, U, hU, hs⟩ := isOpen_pi_iff.mp ho x hx
  let y : ∀ i, X i := fun i => if i ∈ s then x i else b i
  refine ⟨y, hs ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ s := hi
    simpa [y, hi'] using (hU i hi').2
  · apply s.finite_toSet.countable.mono
    intro i hi
    by_contra his
    have his' : i ∉ s := his
    exact hi (by simp [y, his'])

/-- An uncountable discrete Boolean cube is not even sequential, in contrast
with its Fréchet–Urysohn countable-support Σ-subspace. -/
theorem boolean_cube_not_sequential (hι : ¬ Countable ι) :
    ¬ SequentialSpace (ι → Bool) := by
  intro hseq
  let := hseq
  have hc := (isSeqClosed_countableSupport (X := fun _ : ι => Bool) (fun _ => false)).isClosed
  have htrue : (deviationSupport (fun _ : ι => false) (fun _ => true)).Countable :=
    hc.closure_subset ((dense_countableSupport (X := fun _ : ι => Bool) (fun _ => false))
      (fun _ => true))
  have hwhole : (Set.univ : Set ι).Countable := by
    simpa [deviationSupport] using htrue
  exact hι (Set.countable_univ_iff.mp hwhole)

end SigmaFrechet
