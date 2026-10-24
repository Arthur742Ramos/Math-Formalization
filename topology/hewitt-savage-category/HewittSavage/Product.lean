module
public import HewittSavage.Category
public import HewittSavage.Permutation
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section
open Set
namespace HewittSavage

/-- Reindexing by a permutation is a homeomorphism of the actual product topology. -/
def reindexHomeomorph {J X : Type*} [TopologicalSpace X] (σ : Equiv.Perm J) :
    (J → X) ≃ₜ (J → X) := (Homeomorph.piCongrLeft (Y := fun _ : J => X) σ).symm

@[simp] theorem reindexHomeomorph_apply {J X : Type*} [TopologicalSpace X]
    (σ : Equiv.Perm J) (x : J → X) : reindexHomeomorph σ x = x ∘ σ := rfl

/-- Finite coordinate constraints can be moved apart and satisfied simultaneously. -/
theorem coordinate_mixing {J X : Type*} [Infinite J] [TopologicalSpace X]
    {U V : Set (J → X)} (hU : IsOpen U) (hneU : U.Nonempty)
    (hV : IsOpen V) (hneV : V.Nonempty) :
    ∃ σ : Equiv.Perm J, FiniteMoves σ ∧ (U ∩ reindexHomeomorph σ ⁻¹' V).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hneU
  obtain ⟨y, hy⟩ := hneV
  obtain ⟨S, u, hu, hsubU⟩ := isOpen_pi_iff.mp hU x hx
  obtain ⟨T, v, hv, hsubV⟩ := isOpen_pi_iff.mp hV y hy
  obtain ⟨σ, hσ, hsep⟩ := exists_finite_displacement T S
  let z : J → X := fun j => if j ∈ S then x j else y (σ.symm j)
  have hzU : z ∈ U := by
    apply hsubU
    intro j hj
    change (if j ∈ S then x j else y (σ.symm j)) ∈ u j
    rw [ite_eq_left (show j ∈ S from hj)]
    exact (hu j hj).2
  have hzV : reindexHomeomorph σ z ∈ V := by
    apply hsubV
    intro j hj
    change z (σ j) ∈ v j
    simpa [z, hsep j hj] using (hv j hj).2
  exact ⟨σ, hσ, z, hzU, hzV⟩

/-- Category Hewitt–Savage law for an infinite product that is Baire.
The Baire-property set is invariant under every permutation moving finitely many
indices. The product-Baire premise is explicit; no mixing premise is assumed.
This is a qualified form of Bhaskara Rao–Bhaskara Rao (1974), Corollary1. -/
theorem category_zero_one {J X : Type*} [Infinite J] [TopologicalSpace X]
    [BaireSpace (J → X)] {A : Set (J → X)} (hA : BaireMeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm J, FiniteMoves σ → ∀ x, x ∈ A ↔ x ∘ σ ∈ A) :
    IsMeagre A ∨ IsMeagre Aᶜ := by
  refine zero_one_of_mixing
    (fun σ : {σ : Equiv.Perm J // FiniteMoves σ} => reindexHomeomorph σ.val) ?_ hA ?_
  · intro U V hU hneU hV hneV
    obtain ⟨σ, hσ, hm⟩ := coordinate_mixing hU hneU hV hneV
    exact ⟨⟨σ, hσ⟩, hm⟩
  · intro σ x
    exact hinv σ.val σ.property x

/-- The countable product of any Polish space discharges the Baire-product premise. -/
theorem polish_sequence_zero_one {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {A : Set (ℕ → X)} (hA : BaireMeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ℕ, FiniteMoves σ → ∀ x, x ∈ A ↔ x ∘ σ ∈ A) :
    IsMeagre A ∨ IsMeagre Aᶜ := category_zero_one hA hinv

end HewittSavage
