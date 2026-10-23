/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable rational residual completion through finite Fourier--Motzkin LP;
no polynomial complexity claim. -/
module
public import ProtectedSources.RationalLinearTransfer
public import Mathlib.Logic.Equiv.Fin.Basic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev ResidualCompletionRows (m : ℕ) := (Fin 4 × (Fin m × Fin m)) ⊕ Fin m

def residualDecode {α : Type*} {m : ℕ} (x : Fin (m*m) → α) (i j : Fin m) : α :=
  x (finProdFinEquiv (i,j))

def residualEncode {α : Type*} {m : ℕ} (B : Fin m → Fin m → α)
    (u : Fin (m*m)) : α := B (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2

theorem residual_decode_encode {α : Type*} {m : ℕ} (B : Fin m → Fin m → α) :
    residualDecode (residualEncode B) = B := by
  funext i j
  simp only [residualDecode,residualEncode,Equiv.symm_apply_apply]

def residualBasis {m : ℕ} (i j : Fin m) (u : Fin (m*m)) : ℚ :=
  if u=finProdFinEquiv (i,j) then 1 else 0

/-- Tags 0,1 impose upper/lower entry bounds; tags 2,3 impose both
inequalities of skew symmetry. The remaining rows impose actual responses. -/
def residualCompletionSystem {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    RationalLinearSystem (ResidualCompletionRows m) (m*m) where
  coefficient := Sum.elim
    (fun row u => if row.1.val=0 then residualBasis row.2.1 row.2.2 u
      else if row.1.val=1 then -residualBasis row.2.1 row.2.2 u
      else if row.1.val=2 then residualBasis row.2.1 row.2.2 u+residualBasis row.2.2 row.2.1 u
      else -(residualBasis row.2.1 row.2.2 u+residualBasis row.2.2 row.2.1 u))
    (fun i u => ∑ j, residualBasis i j u*q j)
  rightSide := Sum.elim (fun row => if row.1.val=0 ∨ row.1.val=1 then M else 0)
    (fun i => σ-t i)

def ResidualRealConditions {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℝ) : Prop :=
  IsSkew B ∧ (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
    ∀ i, (t i : ℝ)+∑ j, B i j*(q j : ℝ) ≤ (σ : ℝ)

def ResidualRatConditions {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) : Prop :=
  (∀ i j, B i j= -B j i) ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
    ∀ i, t i+∑ j, B i j*q j ≤ σ

theorem residual_basis_real_sum {m : ℕ} (x : Fin (m*m) → ℝ) (i j : Fin m) :
    (∑ u, (residualBasis i j u : ℝ)*x u)=residualDecode x i j := by
  simp [residualBasis,residualDecode,apply_ite]

theorem residual_response_real_sum {m : ℕ} (q : Fin m → ℚ)
    (x : Fin (m*m) → ℝ) (i : Fin m) :
    (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u)=
      ∑ j, residualDecode x i j*(q j : ℝ) := by
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_right_comm,mul_comm (q j : ℝ),←Finset.sum_mul] using
    congrArg (fun z => z*(q j : ℝ)) (residual_basis_real_sum x i j)

theorem residual_completion_real_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (x : Fin (m*m) → ℝ) :
    (residualCompletionSystem q t M σ).RealSatisfies x ↔
      ResidualRealConditions q t M σ (residualDecode x) := by
  have h0 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (0,i,j)) u : ℝ)*x u)=
        residualDecode x i j := by
    change (∑ u, (residualBasis i j u : ℝ)*x u)=_
    exact residual_basis_real_sum x i j
  have h1 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (1,i,j)) u : ℝ)*x u)=
        -residualDecode x i j := by
    change (∑ u, ((-residualBasis i j u : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,residual_basis_real_sum]
  have h2 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (2,i,j)) u : ℝ)*x u)=
        residualDecode x i j+residualDecode x j i := by
    change (∑ u, ((residualBasis i j u+residualBasis j i u : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_add,add_mul,Finset.sum_add_distrib,residual_basis_real_sum]
  have h3 (i j : Fin m) :
      (∑ u, ((residualCompletionSystem q t M σ).coefficient (.inl (3,i,j)) u : ℝ)*x u)=
        -(residualDecode x i j+residualDecode x j i) := by
    change (∑ u, ((-(residualBasis i j u+residualBasis j i u) : ℚ) : ℝ)*x u)=_
    simp only [Rat.cast_neg,Rat.cast_add,neg_mul,add_mul,Finset.sum_neg_distrib,
      Finset.sum_add_distrib,residual_basis_real_sum]
  constructor
  · intro h
    have hub (i j : Fin m) : residualDecode x i j ≤ (M : ℝ) := by
      have hh := h (.inl (0,i,j))
      rw [h0] at hh
      exact hh
    have hlb (i j : Fin m) : -residualDecode x i j ≤ (M : ℝ) := by
      have hh := h (.inl (1,i,j))
      rw [h1] at hh
      exact hh
    have hsk1 (i j : Fin m) : residualDecode x i j+residualDecode x j i ≤ (0 : ℝ) := by
      have hh := h (.inl (2,i,j))
      rw [h2] at hh
      simpa [residualCompletionSystem] using hh
    have hsk2 (i j : Fin m) : -(residualDecode x i j+residualDecode x j i) ≤ (0 : ℝ) := by
      have hh := h (.inl (3,i,j))
      rw [h3] at hh
      simpa [residualCompletionSystem] using hh
    refine ⟨?_,?_,?_⟩
    · intro i j
      linarith [hsk1 i j,hsk2 i j]
    · intro i j
      exact ⟨by linarith [hlb i j],hub i j⟩
    · intro i
      have hi := h (.inr i)
      change (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u) ≤ ((σ-t i : ℚ) : ℝ) at hi
      rw [residual_response_real_sum,Rat.cast_sub] at hi
      linarith
  · rintro ⟨hsk,hb,hr⟩ row
    rcases row with ⟨tag,i,j⟩ | i
    · fin_cases tag
      · change (∑ u, (residualBasis i j u : ℝ)*x u) ≤ (M : ℝ)
        rw [residual_basis_real_sum]
        exact (hb i j).2
      · change (∑ u, ((-residualBasis i j u : ℚ) : ℝ)*x u) ≤ (M : ℝ)
        simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib,residual_basis_real_sum]
        linarith [(hb i j).1]
      · change (∑ u, ((residualBasis i j u+residualBasis j i u : ℚ) : ℝ)*x u) ≤ ((0 : ℚ) : ℝ)
        simp only [Rat.cast_add,add_mul,Finset.sum_add_distrib,residual_basis_real_sum,Rat.cast_zero]
        rw [hsk i j]
        linarith
      · change (∑ u, ((-(residualBasis i j u+residualBasis j i u) : ℚ) : ℝ)*x u) ≤ ((0 : ℚ) : ℝ)
        simp only [Rat.cast_neg,Rat.cast_add,neg_mul,add_mul,Finset.sum_neg_distrib,
          Finset.sum_add_distrib,residual_basis_real_sum,Rat.cast_zero]
        rw [hsk i j]
        linarith
    · change (∑ u, ((∑ j, residualBasis i j u*q j : ℚ) : ℝ)*x u) ≤ ((σ-t i : ℚ) : ℝ)
      rw [residual_response_real_sum,Rat.cast_sub]
      linarith [hr i]

end SparseCompletion
