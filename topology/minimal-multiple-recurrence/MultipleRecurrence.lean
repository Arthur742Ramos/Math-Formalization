/-
Released under the root Apache-2.0 license.
Material Lean proof authorship: OpenAI Codex.
Furstenberg and Weiss, Topological dynamics and combinatorial number theory,
Journal d'Analyse Mathématique 34 (1978), Theorem 1.5.
Glasscock, Koutsogiannis and Richter, Multiplicative combinatorial properties
of return time sets in minimal dynamical systems, Theorems 1.7 and 1.8.
Verification and release evidence is tracked separately by exact source revision.
-/
module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Tactic

@[expose] public section
open Set Function Filter TopologicalSpace

namespace MultipleRecurrence

/-- Every forward interval of length `K + 1` meets the set. -/
def Syndetic (S : Set ℕ) : Prop :=
  ∃ K, ∀ k, ∃ j ≤ K, k + j ∈ S

/-- A syndetic set contains arbitrarily long arithmetic progressions with
    positive common difference. -/
theorem syndetic_arithmetic_progressions (S : Set ℕ) (hS : Syndetic S)
    (d : ℕ) : ∃ a > 0, ∃ b, ∀ i ≤ d, b + i * a ∈ S := by
  classical
  obtain ⟨K, hK⟩ := hS
  let c : ℕ → Fin (K + 1) := fun n =>
    ⟨Classical.choose (hK n), Nat.lt_succ_of_le (Classical.choose_spec (hK n)).1⟩
  have hc_mem (n : ℕ) : n + (c n).val ∈ S := (Classical.choose_spec (hK n)).2
  obtain ⟨a, ha, b, color, hmono⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (d + 1)) c
  refine ⟨a, ha, b + (c b).val, ?_⟩
  intro i hi
  have heq : c (a * i + b) = c b := by
    have hi' := hmono i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hzero := hmono 0 (Finset.mem_range.mpr (Nat.zero_lt_succ d))
    simpa only [nsmul_eq_mul, mul_zero, zero_add] using hi'.trans hzero.symm
  have h := hc_mem (a * i + b)
  rw [heq] at h
  simpa only [Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The common difference can be made arbitrarily large. -/
theorem syndetic_arithmetic_progressions_after (S : Set ℕ) (hS : Syndetic S)
    (d N : ℕ) : ∃ a, N ≤ a ∧ 0 < a ∧ ∃ b, ∀ i ≤ d, b + i * a ∈ S := by
  obtain ⟨a, ha, b, hb⟩ := syndetic_arithmetic_progressions S hS (d * (N + 1))
  refine ⟨a * (N + 1), ?_, ?_, b, ?_⟩
  · nlinarith
  · positivity
  · intro i hi
    have h := hb (i * (N + 1)) (Nat.mul_le_mul_right (N + 1) hi)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- All forward orbits are dense. -/
def ForwardMinimal {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∀ x, Dense (range (fun n : ℕ => f^[n] x))

/-- Compactness makes every orbit's returns to a nonempty open set syndetic. -/
theorem minimal_orbit_returns_syndetic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (hf : Continuous f) (hm : ForwardMinimal f)
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) (x : X) :
    Syndetic {n | f^[n] x ∈ U} := by
  classical
  have hcover : (univ : Set X) ⊆ ⋃ n : ℕ, f^[n] ⁻¹' U := by
    intro y _
    obtain ⟨z, hz, ⟨n, rfl⟩⟩ := (dense_iff_inter_open.mp (hm y)) U hU hne
    exact mem_iUnion.mpr ⟨n, hz⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ => f^[n] ⁻¹' U) (fun n => hU.preimage (hf.iterate n)) hcover
  refine ⟨s.sup id, ?_⟩
  intro k
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hs (mem_univ (f^[k] x)))
  obtain ⟨hjs, hj⟩ := mem_iUnion.mp hj
  refine ⟨j, Finset.le_sup (f := id) hjs, ?_⟩
  simpa only [mem_ofPred_eq, mem_preimage, ← iterate_add_apply, Nat.add_comm j k] using hj

/-- Furstenberg–Weiss multiple recurrence for a minimal system; return steps
    may be required to exceed any prescribed bound. -/
theorem minimal_multiple_recurrence_after {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (hf : Continuous f) (hm : ForwardMinimal f)
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) (d N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∃ x ∈ U, ∀ i ≤ d, f^[i * n] x ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨n, hn, hp, b, hb⟩ := syndetic_arithmetic_progressions_after
    {k | f^[k] x ∈ U} (minimal_orbit_returns_syndetic f hf hm U hU ⟨x, hx⟩ x) d N
  refine ⟨n, hn, hp, f^[b] x, ?_, ?_⟩
  · simpa only [zero_mul, Nat.add_zero, mem_ofPred_eq] using hb 0 (Nat.zero_le d)
  · intro i hi
    simpa only [mem_ofPred_eq, ← iterate_add_apply, Nat.add_comm] using hb i hi

/-- A point returns simultaneously along each finite set of multiples,
    with arbitrarily large positive step, to every open neighborhood. -/
def MultiplyRecurrent {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U → ∀ d N : ℕ,
    ∃ n, N ≤ n ∧ 0 < n ∧ ∀ i ≤ d, f^[i * n] x ∈ U

/-- The open finite-multiple return stage. -/
def returnStage {X : Type*} [TopologicalSpace X] (f : X → X)
    (U : Set X) (d N : ℕ) : Set X :=
  ⋃ n : ℕ, ⋃ (_ : N ≤ n ∧ 0 < n), ⋂ i ∈ Finset.range (d + 1), f^[i * n] ⁻¹' U

theorem isOpen_returnStage {X : Type*} [TopologicalSpace X] (f : X → X)
    (hf : Continuous f) (U : Set X) (hU : IsOpen U) (d N : ℕ) :
    IsOpen (returnStage f U d N) := by
  unfold returnStage
  exact isOpen_iUnion fun n => isOpen_iUnion fun _ =>
    isOpen_biInter_finset fun i _ => hU.preimage (hf.iterate (i * n))

theorem returnStage_mem {X : Type*} [TopologicalSpace X] (f : X → X)
    (U : Set X) (d N : ℕ) (x : X) :
    x ∈ returnStage f U d N ↔ ∃ n, N ≤ n ∧ 0 < n ∧ ∀ i ≤ d, f^[i * n] x ∈ U := by
  simp only [returnStage, mem_iUnion, mem_iInter, Finset.mem_range, mem_preimage]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn.1, hn.2, fun i hi => h i (Nat.lt_succ_of_le hi)⟩
  · rintro ⟨n, hn, hp, h⟩
    exact ⟨n, ⟨hn, hp⟩, fun i hi => h i (Nat.le_of_lt_succ hi)⟩

/-- Minimality gives a dense open stage for each basis set. -/
theorem dense_open_returnStage {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (hf : Continuous f) (hm : ForwardMinimal f)
    (U : Set X) (hU : IsOpen U) (d N : ℕ) :
    IsOpen ((closure U)ᶜ ∪ returnStage f U d N) ∧
      Dense ((closure U)ᶜ ∪ returnStage f U d N) := by
  refine ⟨isClosed_closure.isOpen_compl.union (isOpen_returnStage f hf U hU d N), ?_⟩
  apply dense_iff_inter_open.mpr
  intro V hV hne
  by_cases hVU : (V ∩ U).Nonempty
  · obtain ⟨n, hn, hp, x, hx, hret⟩ :=
      minimal_multiple_recurrence_after f hf hm (V ∩ U) (hV.inter hU) hVU d N
    refine ⟨x, hx.1, Or.inr ((returnStage_mem f U d N x).mpr ?_)⟩
    exact ⟨n, hn, hp, fun i hi => (hret i hi).2⟩
  · obtain ⟨x, hx⟩ := hne
    refine ⟨x, hx, Or.inl ?_⟩
    intro hxc
    have : (V ∩ U).Nonempty := (mem_closure_iff.mp hxc) V hV hx
    exact hVU this

/-- In a second-countable compact system, minimality makes simultaneous
    arithmetic recurrence generic. -/
theorem residual_multiply_recurrent {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] (f : X → X) (hf : Continuous f) (hm : ForwardMinimal f) :
    {x : X | MultiplyRecurrent f x} ∈ residual X := by
  classical
  obtain ⟨B, hBc, hB0, hB⟩ := exists_countable_basis X
  have : Countable B := hBc
  have hstage (U : B) (d N : ℕ) :
      ((closure U.val)ᶜ ∪ returnStage f U.val d N) ∈ residual X :=
    residual_of_dense_open (dense_open_returnStage f hf hm U.val (hB.isOpen U.property) d N).1
      (dense_open_returnStage f hf hm U.val (hB.isOpen U.property) d N).2
  have hall : ∀ᶠ x in residual X, ∀ U : B, ∀ d N : ℕ,
      x ∈ (closure U.val)ᶜ ∪ returnStage f U.val d N :=
    eventually_countable_forall.mpr fun U => eventually_countable_forall.mpr fun d =>
      eventually_countable_forall.mpr fun N => hstage U d N
  filter_upwards [hall] with x hx U hU hxU d N
  obtain ⟨V, hVB, hxV, hVU⟩ := hB.exists_subset_of_mem_open hxU hU
  have hv := hx ⟨V, hVB⟩ d N
  have hvstage : x ∈ returnStage f V d N := by
    rcases hv with hnot | hgood
    · exact False.elim (hnot (subset_closure hxV))
    · exact hgood
  obtain ⟨n, hn, hp, hret⟩ := (returnStage_mem f V d N x).mp hvstage
  exact ⟨n, hn, hp, fun i hi => hVU (hret i hi)⟩

/-- Neighborhood-return times contain positive dilates of every finite set. -/
theorem finite_multipliers_return {X : Type*} [TopologicalSpace X] (f : X → X)
    (x : X) (hx : MultiplyRecurrent f x) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U)
    (F : Finset ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∀ k ∈ F, f^[k * n] x ∈ U := by
  obtain ⟨n, hn, hp, hret⟩ := hx U hU hxU (F.sup id) N
  exact ⟨n, hn, hp, fun k hk => hret k (Finset.le_sup (f := id) hk)⟩

/-- On a nonempty Baire space the generic set contains a dense G-delta set. -/
theorem exists_dense_Gdelta_multiply_recurrent {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [SecondCountableTopology X] [BaireSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hm : ForwardMinimal f) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ C.Nonempty ∧ ∀ x ∈ C, MultiplyRecurrent f x := by
  obtain ⟨C, hC, hG, hd⟩ := mem_residual.mp (residual_multiply_recurrent f hf hm)
  exact ⟨C, hG, hd, hd.nonempty, hC⟩

end MultipleRecurrence
