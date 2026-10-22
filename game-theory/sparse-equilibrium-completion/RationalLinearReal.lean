/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Real soundness of rational Fourier--Motzkin reduction; no complexity claim. -/
module
public import RationalLinearSystem
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalLinearSystem.RealSatisfies {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (x : Fin n → ℝ) : Prop :=
  ∀ i, (∑ j, (S.coefficient i j : ℝ)*x j) ≤ (S.rightSide i : ℝ)

def RationalLinearSystem.realRest {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ) (i : I) : ℝ :=
  ∑ j, (S.coefficient i j.succ : ℝ)*x j

theorem rational_linear_real_split {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin (n+1) → ℝ) (i : I) :
    (∑ j, (S.coefficient i j : ℝ)*x j) =
      (S.slope i : ℝ)*x 0+S.realRest (fun j => x j.succ) i := by
  rw [Fin.sum_univ_succ]
  rfl

theorem rational_linear_real_reduced_zero {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ) (i : S.ZeroRows) :
    (∑ j, (S.reduce.coefficient (.inl i) j : ℝ)*x j)=S.realRest x i.val := rfl

theorem rational_linear_real_reduced_pair {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin n → ℝ)
    (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, (S.reduce.coefficient (.inr (i,h)) j : ℝ)*x j)=
      S.realRest x i.val/(-(S.slope i.val : ℝ))+
      S.realRest x h.val/(S.slope h.val : ℝ) := by
  change (∑ j, ((S.coefficient i.val j.succ/(-S.slope i.val)+
    S.coefficient h.val j.succ/S.slope h.val : ℚ) : ℝ)*x j)=_
  push_cast
  simp only [add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,←Finset.sum_div,
    RationalLinearSystem.realRest]

theorem rational_linear_real_reduce_feasible {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (x : Fin (n+1) → ℝ)
    (hx : S.RealSatisfies x) :
    S.reduce.RealSatisfies (fun j => x j.succ) := by
  intro row
  rcases row with i | ⟨i,h⟩
  · have hi := hx i.val
    rw [rational_linear_real_split] at hi
    have hz : (S.slope i.val : ℝ)=0 := by exact_mod_cast i.property
    rw [hz,zero_mul,zero_add] at hi
    rw [rational_linear_real_reduced_zero]
    exact hi
  · have hi := hx i.val
    have hh := hx h.val
    rw [rational_linear_real_split] at hi hh
    have hil : (S.slope i.val : ℝ)<0 := by exact_mod_cast i.property
    have hhu : (0 : ℝ)<(S.slope h.val : ℝ) := by exact_mod_cast h.property
    have hden : (0 : ℝ)< -(S.slope i.val : ℝ) := neg_pos.mpr hil
    have hli := div_le_div_of_nonneg_right hi (le_of_lt hden)
    have hhi := div_le_div_of_nonneg_right hh (le_of_lt hhu)
    have hel : ((S.slope i.val : ℝ)*x 0+S.realRest (fun j => x j.succ) i.val)/
        (-(S.slope i.val : ℝ)) =
        -x 0+S.realRest (fun j => x j.succ) i.val/(-(S.slope i.val : ℝ)) := by
      field_simp [ne_of_lt hil]
      ring
    have heu : ((S.slope h.val : ℝ)*x 0+S.realRest (fun j => x j.succ) h.val)/
        (S.slope h.val : ℝ) =
        x 0+S.realRest (fun j => x j.succ) h.val/(S.slope h.val : ℝ) := by
      field_simp [ne_of_gt hhu]
    rw [hel] at hli
    rw [heu] at hhi
    rw [rational_linear_real_reduced_pair]
    change _ ≤ ((S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val : ℚ) : ℝ)
    push_cast
    linarith

theorem rational_linear_real_cast_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) :
    S.RealSatisfies (fun j => (q j : ℝ)) ↔ S.Satisfies q := by
  constructor
  · intro h i
    have hi : ((∑ j, S.coefficient i j*q j : ℚ) : ℝ) ≤ (S.rightSide i : ℝ) := by
      simpa only [Rat.cast_sum,Rat.cast_mul] using h i
    exact_mod_cast hi
  · intro h i
    have hi := h i
    have hR : ((∑ j, S.coefficient i j*q j : ℚ) : ℝ) ≤ (S.rightSide i : ℝ) := by
      exact_mod_cast hi
    simpa only [Rat.cast_sum,Rat.cast_mul] using hR

theorem rational_linear_real_zero_iff {I : Type*}
    (S : RationalLinearSystem I 0) (x : Fin 0 → ℝ) :
    S.RealSatisfies x ↔ ∀ i, (0 : ℚ) ≤ S.rightSide i := by
  simp only [RationalLinearSystem.RealSatisfies,Finset.univ_eq_empty,Finset.sum_empty,
    Rat.cast_nonneg]

end SparseCompletion
