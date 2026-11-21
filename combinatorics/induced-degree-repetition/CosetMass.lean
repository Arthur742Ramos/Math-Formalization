module

import PFR.TorsionEndgame
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs

public section
namespace InducedDegreeRepetition

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Unnormalized mass of a finite event. -/
@[expose] noncomputable def massOn (w : G → ℝ) (A : Set G) : ℝ := by
  classical exact ∑ x, if x ∈ A then w x else 0

/-- The covering-to-concentration step in Lemma 6, with the exponent from [6, Thm. 1.1].
The event A can already be a translate of the set delivered by weighted BSG. -/
theorem coset_mass_of_small_doubling (q : ℕ) (hq : 2 ≤ q) (htor : ∀ x : G, q • x = 0)
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (A : Set G) (hne : A.Nonempty) (K : ℝ)
    (hd : (Nat.card (A + A) : ℝ) ≤ K * A.ncard) :
    ∃ (H : AddSubgroup G) (z : G), (H : Set G).ncard ≤ A.ncard ∧
      massOn w A ≤ (q : ℝ) * K ^ (256*q^3+1) * massOn w {x | x - z ∈ H} := by
  classical
  obtain ⟨H, c, hc, hH, hcover⟩ := torsion_PFR hq htor hne hd
  let F : G → ℝ := fun z => massOn w {x | x - z ∈ H}
  obtain ⟨z, _, hz⟩ := univ.exists_max_image F univ_nonempty
  refine ⟨H, z, hH, ?_⟩
  have hpos (a : G) : 0 ≤ F a := by
    exact sum_nonneg fun x _ => by dsimp; split <;> simp [hw]
  have hs : massOn w A ≤ ∑ y ∈ c.toFinset, F y := by
    simp only [F, massOn, Set.mem_ofPred_eq]
    rw [sum_comm]
    apply sum_le_sum
    intro x _
    by_cases hx : x ∈ A
    · obtain ⟨y,hy,h,hh,rfl⟩ := Set.mem_add.mp (hcover hx)
      rw [ite_eq_left hx]
      apply le_trans _ (single_le_sum (f := fun t => if y+h-t ∈ H then w (y+h) else 0)
        (fun t _ => by split <;> simp [hw]) (Set.mem_toFinset.mpr hy))
      change h ∈ H at hh
      simp [hh]
    · simp only [ite_eq_right hx]
      exact sum_nonneg fun t _ => by split <;> simp [hw]
  calc
    _ ≤ _ := hs
    _ ≤ ∑ _y ∈ c.toFinset, F z := sum_le_sum fun y _ => hz _ (mem_univ y)
    _ = (Nat.card c : ℝ) * F z := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc.le (hpos z)

end InducedDegreeRepetition
