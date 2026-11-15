/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.DiscreteCorrelation
public import Mathlib.Order.LiminfLimsup

/-! # The literal finite and asymptotic statement of Erdős problem 36

`minimumOverlap N` minimizes the maximum number of representations of an
integer as `a-b` over equal-size partitions of `{1,…,2N}`. Its normalized
liminf is `discreteOverlapConstant`. The exact cell embedding proves the
lower-bound transfer from the continuous binary constant, without invoking
an equality between the continuous and discrete variational problems.
-/

@[expose] public section

namespace ErdosOverlap.Discrete

open Set Filter

noncomputable section

theorem maximumCount_eq_iSup (A B : Finset ℤ) :
    maximumCount A B = ⨆ k : ℤ, differenceCount A B k := by
  have hb : BddAbove (Set.range (differenceCount A B)) :=
    ⟨A.card, by rintro y ⟨k,rfl⟩; exact differenceCount_le_card_left A B k⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro p _
    exact le_ciSup hb _
  · exact ciSup_le (differenceCount_le_maximumCount A B)

/-- Equal cardinalities together with the disjoint full union are exactly
the explicit `N`-element hypotheses used in the cell embedding. -/
theorem balancedPartition_iff {N : ℕ} {A B : Finset ℤ} :
    BalancedPartition N A B ↔ Disjoint A B ∧
      A ∪ B = Finset.Icc 1 (2*(N : ℤ)) ∧ A.card = B.card := by
  constructor
  · intro h
    exact ⟨h.disjoint,h.union,h.card_left.trans h.card_right.symm⟩
  · rintro ⟨hd,hu,hcard⟩
    have hc := congrArg Finset.card hu
    rw [Finset.card_union_of_disjoint hd, Int.card_Icc] at hc
    have hsize : (2*(N : ℤ)+1-1).toNat = 2*N := by
      rw [show 2*(N : ℤ)+1-1 = ((2*N : ℕ) : ℤ) by push_cast; ring]
      exact Int.toNat_natCast _
    rw [hsize] at hc
    exact ⟨hd,hu,by omega,by omega⟩

theorem consecutivePartition (N : ℕ) :
    BalancedPartition N (Finset.Icc 1 (N : ℤ))
      (Finset.Icc ((N : ℤ)+1) (2*(N : ℤ))) where
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro j hj₀ hj₁
    obtain ⟨_,hj₀⟩ := Finset.mem_Icc.mp hj₀
    obtain ⟨hj₁,_⟩ := Finset.mem_Icc.mp hj₁
    omega
  union := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  card_left := by simp [Int.card_Icc]
  card_right := by
    rw [Int.card_Icc, show 2*(N : ℤ)+1-((N : ℤ)+1) = (N : ℤ) by ring]
    exact Int.toNat_natCast N

def finiteMaximumValues (N : ℕ) : Set ℕ :=
  {z | ∃ A B : Finset ℤ, BalancedPartition N A B ∧ maximumCount A B = z}

def minimumOverlap (N : ℕ) : ℕ := sInf (finiteMaximumValues N)

def minimumOverlapQuotient (N : ℕ) : ℝ := (minimumOverlap N : ℝ)/(N : ℝ)

def discreteOverlapConstant : ℝ := Filter.liminf minimumOverlapQuotient Filter.atTop

/-- An explicit equality with the supremum/minimum formulation of the
integer problem, using only disjointness, the full union and equal sizes. -/
theorem minimumOverlap_eq_literal (N : ℕ) :
    minimumOverlap N = sInf {z : ℕ | ∃ A B : Finset ℤ,
      Disjoint A B ∧ A ∪ B = Finset.Icc 1 (2*(N : ℤ)) ∧
      A.card = B.card ∧ (⨆ k : ℤ, differenceCount A B k) = z} := by
  unfold minimumOverlap
  congr 1
  ext z
  constructor
  · rintro ⟨A,B,hp,hz⟩
    refine ⟨A,B,hp.disjoint,hp.union,hp.card_left.trans hp.card_right.symm,?_⟩
    rw [← maximumCount_eq_iSup]
    exact hz
  · rintro ⟨A,B,hd,hu,hcard,hz⟩
    refine ⟨A,B,balancedPartition_iff.mpr ⟨hd,hu,hcard⟩,?_⟩
    rw [maximumCount_eq_iSup]
    exact hz

theorem finiteMaximumValues_nonempty (N : ℕ) : (finiteMaximumValues N).Nonempty := by
  exact ⟨_, _, _, consecutivePartition N, rfl⟩

theorem minimumOverlap_attained (N : ℕ) :
    ∃ A B : Finset ℤ, BalancedPartition N A B ∧ maximumCount A B = minimumOverlap N :=
  Nat.sInf_mem (finiteMaximumValues_nonempty N)

theorem minimumOverlap_le_maximumCount {N : ℕ} {A B : Finset ℤ}
    (hp : BalancedPartition N A B) : minimumOverlap N ≤ maximumCount A B :=
  Nat.sInf_le ⟨A,B,hp,rfl⟩

theorem minimumOverlap_le (N : ℕ) : minimumOverlap N ≤ N := by
  obtain ⟨A,B,hp,hv⟩ := minimumOverlap_attained N
  rw [← hv, ← hp.card_left]
  exact maximumCount_le_card_left A B

theorem minimumOverlapQuotient_nonneg (N : ℕ) : 0 ≤ minimumOverlapQuotient N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem minimumOverlapQuotient_le_one (N : ℕ) : minimumOverlapQuotient N ≤ 1 := by
  by_cases hN : N=0
  · simp [minimumOverlapQuotient,hN]
  · have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hn).mpr
    simpa only [one_mul] using (show (minimumOverlap N : ℝ) ≤ (N : ℝ) by
      exact_mod_cast minimumOverlap_le N)

theorem erdosOverlapConstant_le_minimumOverlapQuotient {N : ℕ} (hN : 0 < N) :
    erdosOverlapConstant ≤ minimumOverlapQuotient N := by
  obtain ⟨A,B,hp,hv⟩ := minimumOverlap_attained N
  unfold minimumOverlapQuotient
  rw [← hv]
  exact erdosOverlapConstant_le_normalizedMaximum hN hp

/-- The lower-bound direction needed for the original asymptotic problem. -/
theorem erdosOverlapConstant_le_discreteOverlapConstant :
    erdosOverlapConstant ≤ discreteOverlapConstant := by
  apply Filter.le_liminf_of_le
    (Filter.isCoboundedUnder_ge_of_le Filter.atTop minimumOverlapQuotient_le_one)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  exact erdosOverlapConstant_le_minimumOverlapQuotient (by omega)

theorem relaxedOverlapConstant_le_discreteOverlapConstant :
    relaxedOverlapConstant ≤ discreteOverlapConstant :=
  relaxedOverlapConstant_le_erdosOverlapConstant.trans
    erdosOverlapConstant_le_discreteOverlapConstant

/-- A uniform continuous lower bound yields an actual integer difference
with at least that many representations in every finite partition. -/
theorem exists_difference_ge_of_constant_le {c : ℝ} (hc : c ≤ erdosOverlapConstant)
    {N : ℕ} (hN : 0 < N) {A B : Finset ℤ} (hp : BalancedPartition N A B) :
    ∃ k : ℤ, c*(N : ℝ) ≤ (differenceCount A B k : ℝ) := by
  have hA : A.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_left] using hN)
  have hB : B.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_right] using hN)
  obtain ⟨k,hk⟩ := maximumCount_attained hA hB
  refine ⟨k,?_⟩
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h := (le_div_iff₀ hn).mp
    (hc.trans (erdosOverlapConstant_le_normalizedMaximum hN hp))
  simpa only [hk] using h

theorem exists_difference_gt_of_lt_constant {c : ℝ} (hc : c < erdosOverlapConstant)
    {N : ℕ} (hN : 0 < N) {A B : Finset ℤ} (hp : BalancedPartition N A B) :
    ∃ k : ℤ, c*(N : ℝ) < (differenceCount A B k : ℝ) := by
  have hA : A.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_left] using hN)
  have hB : B.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_right] using hN)
  obtain ⟨k,hk⟩ := maximumCount_attained hA hB
  refine ⟨k,?_⟩
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h := (lt_div_iff₀ hn).mp
    (hc.trans_le (erdosOverlapConstant_le_normalizedMaximum hN hp))
  simpa only [hk] using h

end
end ErdosOverlap.Discrete
