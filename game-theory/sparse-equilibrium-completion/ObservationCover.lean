/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ExtraMomentAllMass

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def offDiagonalIntervals {ν : Type*} (lo hi A : ν → ν → ℝ) : Prop :=
  ∀ a b, a ≠ b → lo a b ≤ A a b ∧ A a b ≤ hi a b

def freeResidualIntervals {ι α : Type*} (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ) : Prop :=
  ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -M ∧ hi (.inr i) (.inr j)=M

def intervalConstraintEdge {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) (a b : ν) : Prop :=
  a ≠ b ∧ (lo a b ≠ -M ∨ hi a b ≠ M)

theorem free_residual_iff_anchor_cover {ι α : Type*}
    (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ) :
    freeResidualIntervals lo hi M ↔
      ∀ a b, intervalConstraintEdge lo hi M a b →
        (∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h := by
  constructor
  · intro hc a b he
    cases a with
    | inl h => exact Or.inl ⟨h,rfl⟩
    | inr i =>
      cases b with
      | inl h => exact Or.inr ⟨h,rfl⟩
      | inr j =>
        have hij : i ≠ j := fun hij => he.1 (congrArg Sum.inr hij)
        have hh := hc i j hij
        exact False.elim (he.2.elim (fun hn => hn hh.1) (fun hn => hn hh.2))
  · intro hc i j hij
    have he : Sum.inr i ≠ (Sum.inr j : α ⊕ ι) := fun he => hij (Sum.inr.inj he)
    by_contra hn
    have hbad : lo (.inr i) (.inr j) ≠ -M ∨ hi (.inr i) (.inr j) ≠ M := by
      tauto
    obtain (⟨h,hh⟩ | ⟨h,hh⟩) := hc (.inr i) (.inr j) ⟨he,hbad⟩ <;> cases hh

theorem cover_intervals_preserved {ι α : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B B' : ι → ι → ℝ) (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M : ℝ)
    (hc : freeResidualIntervals lo hi M) (hI : offDiagonalIntervals lo hi (blockMatrix K D B))
    (hB' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) :
    offDiagonalIntervals lo hi (blockMatrix K D B') := by
  intro a b hab
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hI (.inl h) (.inl h') hab
    | inr j => exact hI (.inl h) (.inr j) hab
  | inr i =>
    cases b with
    | inl h => exact hI (.inr i) (.inl h) hab
    | inr j =>
      have hij : i ≠ j := fun he => hab (congrArg Sum.inr he)
      have hh := hc i j hij
      change lo (.inr i) (.inr j) ≤ B' i j ∧ B' i j ≤ hi (.inr i) (.inr j)
      rw [hh.1,hh.2]
      exact hB' i j

theorem anchor_incident_entries_preserved {ι α : Type*} (K : α → α → ℝ)
    (D : ι → α → ℝ) (B B' : ι → ι → ℝ) (a b : α ⊕ ι)
    (hc : (∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) :
    blockMatrix K D B' a b=blockMatrix K D B a b := by
  rcases hc with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · cases b <;> rfl
  · cases a <;> rfl

end
end SparseCompletion
