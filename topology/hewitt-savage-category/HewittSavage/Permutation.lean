module
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic

@[expose] public section
open Set Equiv
namespace HewittSavage

/-- Finitely many indices are moved, relative to the identity permutation. -/
abbrev FiniteMoves {J : Type*} (σ : Equiv.Perm J) : Prop := {j | σ j ≠ j}.Finite

theorem finiteMoves_one {J : Type*} : FiniteMoves (1 : Equiv.Perm J) := by
  simp [FiniteMoves]

theorem finiteMoves_mul {J : Type*} {σ τ : Equiv.Perm J}
    (hσ : FiniteMoves σ) (hτ : FiniteMoves τ) : FiniteMoves (σ * τ) := by
  refine (hσ.union hτ).subset ?_
  intro j hj
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hn
  exact hj (by simp [Equiv.Perm.mul_apply, hn.1, hn.2])

theorem finiteMoves_swap {J : Type*} [DecidableEq J] (a b : J) :
    FiniteMoves (Equiv.swap a b) := by
  refine ((finite_singleton b).insert a).subset ?_
  intro j hj
  by_contra hn
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hn
  exact hj (by simp [Equiv.swap_apply_def, hn.1, hn.2])

/-- A finite-support permutation moves every index of S outside the finite set T. -/
theorem exists_finite_displacement {J : Type*} [Infinite J] (S T : Finset J) :
    ∃ σ : Equiv.Perm J, FiniteMoves σ ∧ ∀ j ∈ S, σ j ∉ T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, finiteMoves_one, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨σ, hσ, hS⟩ := ih
    obtain ⟨b, hb⟩ := (S ∪ {a} ∪ T.image σ.symm).exists_notMem
    have hb' : (b ∉ S ∧ b ≠ a) ∧ b ∉ T.image σ.symm := by
      simpa only [Finset.mem_union, Finset.mem_singleton, not_or] using hb
    have hbS : b ∉ S := hb'.1.1
    have hbT : σ b ∉ T := by
      intro h
      exact hb'.2 (Finset.mem_image.mpr ⟨σ b, h, σ.symm_apply_apply b⟩)
    refine ⟨σ * Equiv.swap a b, finiteMoves_mul hσ (finiteMoves_swap a b), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa [Equiv.Perm.mul_apply] using hbT
    · have hja : j ≠ a := fun he => ha (he ▸ hj)
      have hjb : j ≠ b := fun he => hbS (he ▸ hj)
      simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hja, hjb] using hS j hj

end HewittSavage
