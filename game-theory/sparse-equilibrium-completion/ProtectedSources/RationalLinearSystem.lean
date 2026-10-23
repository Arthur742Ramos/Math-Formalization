/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Classical Fourier–Motzkin elimination; no polynomial complexity claim. -/
module
public import ProtectedSources.RationalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalLinearSystem (I : Type*) (n : ℕ) where
  coefficient : I → Fin n → ℚ
  rightSide : I → ℚ

def RationalLinearSystem.Satisfies {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) : Prop :=
  ∀ i, (∑ j, S.coefficient i j*q j) ≤ S.rightSide i

instance rationalLinearSatisfiesDecidable {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) : Decidable (S.Satisfies q) := by
  unfold RationalLinearSystem.Satisfies
  infer_instance

def RationalLinearSystem.slope {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (i : I) : ℚ := S.coefficient i 0

def RationalLinearSystem.rest {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : I) : ℚ :=
  ∑ j, S.coefficient i j.succ*q j

theorem rational_linear_cons_response {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (x : ℚ) (i : I) :
    (∑ j, S.coefficient i j*Fin.cons (α := fun _ => ℚ) x q j)=S.slope i*x+S.rest q i := by
  rw [Fin.sum_univ_succ]
  rfl

theorem rational_linear_cons_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (x : ℚ) :
    S.Satisfies (Fin.cons (α := fun _ => ℚ) x q) ↔ ∀ i, S.slope i*x+S.rest q i ≤ S.rightSide i := by
  simp only [RationalLinearSystem.Satisfies,rational_linear_cons_response]

abbrev RationalLinearSystem.ZeroRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // S.slope i=0}

abbrev RationalLinearSystem.LowerRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // S.slope i < 0}

abbrev RationalLinearSystem.UpperRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  {i : I // 0 < S.slope i}

abbrev RationalLinearSystem.ReducedRows {I : Type*} {n : ℕ} (S : RationalLinearSystem I (n+1)) :=
  S.ZeroRows ⊕ (S.LowerRows × S.UpperRows)

def RationalLinearSystem.reduce {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) : RationalLinearSystem S.ReducedRows n where
  coefficient := Sum.elim (fun i j => S.coefficient i.val j.succ)
    (fun a j => S.coefficient a.1.val j.succ/(-S.slope a.1.val)+
      S.coefficient a.2.val j.succ/S.slope a.2.val)
  rightSide := Sum.elim (fun i => S.rightSide i.val)
    (fun a => S.rightSide a.1.val/(-S.slope a.1.val)+S.rightSide a.2.val/S.slope a.2.val)

theorem rational_linear_reduced_zero {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.ZeroRows) :
    (∑ j, S.reduce.coefficient (.inl i) j*q j)=S.rest q i.val := rfl

theorem rational_linear_reduced_pair {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, S.reduce.coefficient (.inr (i,h)) j*q j)=
      S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val := by
  change (∑ j, (S.coefficient i.val j.succ/(-S.slope i.val)+
      S.coefficient h.val j.succ/S.slope h.val)*q j)=_
  simp only [add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,←Finset.sum_div,
    RationalLinearSystem.rest]


def RationalLinearSystem.Eliminated {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) : Prop :=
  (∀ i, S.slope i=0 → S.rest q i ≤ S.rightSide i) ∧
    ∀ i, S.slope i < 0 → ∀ h, 0 < S.slope h →
      (S.rightSide i-S.rest q i)/S.slope i ≤ (S.rightSide h-S.rest q h)/S.slope h

theorem rational_linear_pair_inequality {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) (i : S.LowerRows) (h : S.UpperRows) :
    (∑ j, S.reduce.coefficient (.inr (i,h)) j*q j) ≤ S.reduce.rightSide (.inr (i,h)) ↔
      (S.rightSide i.val-S.rest q i.val)/S.slope i.val ≤
        (S.rightSide h.val-S.rest q h.val)/S.slope h.val := by
  rw [rational_linear_reduced_pair]
  change S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val ≤
    S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val ↔ _
  have he : (S.rightSide i.val-S.rest q i.val)/S.slope i.val-
      (S.rightSide h.val-S.rest q h.val)/S.slope h.val=
      S.rest q i.val/(-S.slope i.val)+S.rest q h.val/S.slope h.val-
      (S.rightSide i.val/(-S.slope i.val)+S.rightSide h.val/S.slope h.val) := by
    simp only [div_neg]
    ring
  constructor <;> intro hh <;> linarith

theorem rational_linear_reduce_iff {I : Type*} {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) :
    S.reduce.Satisfies q ↔ S.Eliminated q := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (.inl ⟨i,hi⟩)
    · intro i hi j hj
      exact (rational_linear_pair_inequality S q ⟨i,hi⟩ ⟨j,hj⟩).mp
        (h (.inr (⟨i,hi⟩,⟨j,hj⟩)))
  · rintro ⟨hz,hp⟩ a
    rcases a with i | ⟨i,h⟩
    · exact hz i.val i.property
    · exact (rational_linear_pair_inequality S q i h).mpr (hp i.val i.property h.val h.property)

end SparseCompletion
