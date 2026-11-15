/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.PhaseForm
public import ErdosOverlap.Gram.PhaseData

/-!
# Exact finite lag matrices

An off-diagonal lag coefficient is split equally between its symmetric
matrix entries. The resulting trace is proved equal to the one-sided lag
sum used by the continuous tent identity.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

def distanceIndex {N : ℕ} (i j : Fin (N+1)) : Fin (N+1) :=
  ⟨natDistance i.val j.val, by
    have hi := i.isLt
    have hj := j.isLt
    unfold natDistance
    split_ifs <;> omega⟩

noncomputable def lagMatrix {N : ℕ} (k i j : Fin (N+1)) : ℝ :=
  if k = distanceIndex i j then (if i = j then 1 else 1/2) else 0

noncomputable def lagTrace {N : ℕ} (X : Fin (N+1) → Fin (N+1) → ℝ)
    (k : Fin (N+1)) : ℝ := tracePair (lagMatrix k) X

theorem lagMatrix_directed {N : ℕ} (k i j : Fin (N+1)) :
    lagMatrix k i j =
      ((if i.val + k.val = j.val then 1 else 0) +
        (if j.val + k.val = i.val then 1 else 0)) / 2 := by
  simp only [lagMatrix, Fin.ext_iff, distanceIndex, natDistance]
  split_ifs <;> norm_num at * <;> omega

theorem directedLag_sum {N k : ℕ} (hk : k ≤ N) (X : ℕ → ℕ → ℝ) :
    (∑ i : Fin (N+1), ∑ j : Fin (N+1),
      if i.val + k = j.val then X i.val j.val else 0) =
      ∑ i ∈ Finset.range (N-k+1), X i (i+k) := by
  have hinner (i : ℕ) : (∑ j : Fin (N+1),
      if i + k = j.val then X i j.val else 0) =
      if i+k < N+1 then X i (i+k) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if i+k=j then X i j else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i+k<N+1 then X i (i+k) else 0)]
  have hfilter : (Finset.range (N+1)).filter (fun i => i+k < N+1) =
      Finset.range (N-k+1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]

theorem lagTrace_eq_range {N : ℕ} (X : ℕ → ℕ → ℝ)
    (hX : ∀ i j, X i j = X j i) (k : Fin (N+1)) :
    lagTrace (fun i j : Fin (N+1) => X i.val j.val) k =
      ∑ i ∈ Finset.range (N-k.val+1), X i (i+k.val) := by
  have hk : k.val ≤ N := Nat.le_of_lt_succ k.isLt
  have hswap : (∑ i : Fin (N+1), ∑ j : Fin (N+1),
      if j.val + k.val = i.val then X i.val j.val else 0) =
      ∑ i : Fin (N+1), ∑ j : Fin (N+1),
        if i.val + k.val = j.val then X i.val j.val else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hX j.val i.val]
  unfold lagTrace tracePair
  simp_rw [lagMatrix_directed]
  simp only [div_mul_eq_mul_div, add_mul, ite_mul, zero_mul, one_mul, add_div]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hswap, directedLag_sum hk X]
  ring

theorem weighted_lagTrace {N : ℕ} (X : Fin (N+1) → Fin (N+1) → ℝ)
    (w : Fin (N+1) → ℝ) :
    (∑ k, w k * lagTrace X k) =
      tracePair (fun i j => w (distanceIndex i j) * (if i = j then 1 else 1/2)) X := by
  unfold lagTrace tracePair
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [lagMatrix, mul_assoc, mul_ite]

end ErdosOverlap.Gram
