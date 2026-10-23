/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.CoveredWitness
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def relabelWeights {ν μ : Type*} (e : ν ≃ μ) (q : ν → ℝ) : μ → ℝ := fun i => q (e.symm i)

def relabelMatrix {ν μ : Type*} (e : ν ≃ μ) (A : ν → ν → ℝ) : μ → μ → ℝ :=
  fun i j => A (e.symm i) (e.symm j)

theorem relabel_mass {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ) (q : ν → ℝ) :
    (∑ i, relabelWeights e q i)=∑ i, q i := Equiv.sum_comp e.symm q

theorem relabel_response {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ)
    (A : ν → ν → ℝ) (q : ν → ℝ) (i : μ) :
    response (relabelMatrix e A) (relabelWeights e q) i=response A q (e.symm i) := by
  exact Equiv.sum_comp e.symm (fun j => A (e.symm i) j*q j)

theorem relabel_support_card {ν μ : Type*} [Fintype ν] [Fintype μ] (e : ν ≃ μ) (q : ν → ℝ) :
    (Finset.univ.filter fun i => relabelWeights e q i ≠ 0).card=
      (Finset.univ.filter fun i => q i ≠ 0).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Equiv.sum_comp e.symm (fun j => if q j ≠ 0 then (1 : ℕ) else 0)

theorem relabel_skew {ν μ : Type*} (e : ν ≃ μ) (A : ν → ν → ℝ) (hA : IsSkew A) :
    IsSkew (relabelMatrix e A) := fun i j => hA (e.symm i) (e.symm j)

theorem relabel_intervals {ν μ : Type*} (e : ν ≃ μ) (lo hi A : ν → ν → ℝ) :
    offDiagonalIntervals (relabelMatrix e lo) (relabelMatrix e hi) (relabelMatrix e A) ↔
      offDiagonalIntervals lo hi A := by
  constructor
  · intro h i j hij
    have hne : e i ≠ e j := fun he => hij (e.injective he)
    simpa only [relabelMatrix,e.symm_apply_apply] using h (e i) (e j) hne
  · intro h i j hij
    exact h (e.symm i) (e.symm j) (fun he => hij (e.symm.injective he))

def coverEquiv {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] :
    (Fin (Fintype.card C) ⊕ (Cᶜ : Set ν)) ≃ ν :=
   (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _)).trans (Equiv.Set.sumCompl C)

theorem cover_equiv_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (h : Fin (Fintype.card C)) :
    coverEquiv C (.inl h) ∈ C := by
  change ((Fintype.equivFin C).symm h).val ∈ C
  exact ((Fintype.equivFin C).symm h).property

theorem cover_equiv_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (i : (Cᶜ : Set ν)) :
    coverEquiv C (.inr i)=i.val := rfl

theorem cover_equiv_inverse_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)] (v : ν) (hv : v ∈ C) :
    ∃ h, (coverEquiv C).symm v=Sum.inl h := by
  classical
  cases he : (coverEquiv C).symm v with
  | inl h => exact ⟨h,rfl⟩
  | inr i =>
    have hh : v=i.val := by
      have h0 := congrArg (coverEquiv C) he
      simpa only [Equiv.apply_symm_apply,cover_equiv_residual] using h0
    exact False.elim (i.property (hh ▸ hv))

def intervalVertexCover {ν : Type*} (C : Set ν) (lo hi : ν → ν → ℝ) (M : ℝ) : Prop :=
  ∀ i j, intervalConstraintEdge lo hi M i j → i ∈ C ∨ j ∈ C

theorem arbitrary_cover_free_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (lo hi : ν → ν → ℝ) (M : ℝ) (hc : intervalVertexCover C lo hi M) :
    freeResidualIntervals (relabelMatrix (coverEquiv C).symm lo)
      (relabelMatrix (coverEquiv C).symm hi) M := by
  intro i j hij
  have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  by_contra hn
  have hbad : lo i.val j.val ≠ -M ∨ hi i.val j.val ≠ M := by
    change ¬(lo i.val j.val= -M ∧ hi i.val j.val=M) at hn
    tauto
  rcases hc i.val j.val ⟨hv,hbad⟩ with h | h
  · exact i.property h
  · exact j.property h

theorem split_weights {ν α ι : Type*} (e : (α ⊕ ι) ≃ ν) (x : ν → ℝ) :
    relabelWeights e.symm x=blockWeights (fun h => x (e (.inl h))) (fun i => x (e (.inr i))) := by
  funext a
  cases a <;> rfl

theorem split_skew_matrix {ν α ι : Type*} (e : (α ⊕ ι) ≃ ν) (A : ν → ν → ℝ) (hA : IsSkew A) :
    relabelMatrix e.symm A=blockMatrix (fun h h' => A (e (.inl h)) (e (.inl h')))
      (fun i h => A (e (.inr i)) (e (.inl h))) (fun i j => A (e (.inr i)) (e (.inr j))) := by
  funext a b
  cases a with
  | inl h =>
    cases b with
    | inl h' => rfl
    | inr j => exact hA _ _
  | inr i => cases b <;> rfl

theorem cover_relabel_on_residual {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (p : Fin (Fintype.card C) → ℝ) (q : (Cᶜ : Set ν) → ℝ) (i : (Cᶜ : Set ν)) :
    relabelWeights (coverEquiv C) (blockWeights p q) i.val=q i := by
  rw [←cover_equiv_residual C i]
  simp only [relabelWeights,Equiv.symm_apply_apply,blockWeights,Sum.elim_inr]

theorem cover_relabel_on_anchor {ν : Type*} [Fintype ν] (C : Set ν) [DecidablePred (· ∈ C)]
    (x : ν → ℝ) (q : (Cᶜ : Set ν) → ℝ) (v : ν) (hv : v ∈ C) :
    relabelWeights (coverEquiv C)
      (blockWeights (fun h => x (coverEquiv C (.inl h))) q) v=x v := by
  obtain ⟨h,he⟩ := cover_equiv_inverse_anchor C v hv
  have hv' : v=coverEquiv C (.inl h) := by
    have hh := congrArg (coverEquiv C) he
    simpa only [Equiv.apply_symm_apply] using hh
  rw [hv']
  simp only [relabelWeights,Equiv.symm_apply_apply,blockWeights,Sum.elim_inl]

end
end SparseCompletion
