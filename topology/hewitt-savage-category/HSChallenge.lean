module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.MetricSpace.Polish


@[expose] public section
open Set Filter
open scoped Topology
namespace HewittSavage

/-- The open approximation has a nonempty region when the Baire set is nonmeagre. -/
theorem open_residual_witness {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∃ S : Set X, S ∈ residual X ∧ U ∩ S ⊆ A := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hUne : U.Nonempty := by
    by_contra he
    apply hn
    change ∀ᶠ x in residual X, x ∉ A
    filter_upwards [hAU.mem_iff] with x hx
    exact fun hxa => he ⟨x, hx.mp hxa⟩
  refine ⟨U, hU, hUne, {x | x ∈ A ↔ x ∈ U}, hAU.mem_iff, ?_⟩
  exact fun x hx => hx.2.mpr hx.1

/-- An internal category zero-one argument. The product theorem proves, rather than
assumes, the required mixing condition for its coordinate homeomorphisms. -/
theorem zero_one_of_mixing {X I : Type*} [TopologicalSpace X] [BaireSpace X]
    (h : I → X ≃ₜ X)
    (hmix : ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ i, (U ∩ h i ⁻¹' V).Nonempty)
    {A : Set X} (hA : BaireMeasurableSet A)
    (hinv : ∀ i x, x ∈ A ↔ h i x ∈ A) : IsMeagre A ∨ IsMeagre Aᶜ := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨U, hU, hUne, S, hS, hSA⟩ := open_residual_witness hA hn.1
  obtain ⟨V, hV, hVne, T, hT, hTA⟩ := open_residual_witness hA.compl hn.2
  obtain ⟨i, hi⟩ := hmix U V hU hUne hV hVne
  have hpre : h i ⁻¹' T ∈ residual X :=
    (tendsto_residual_of_isOpenMap (h i).continuous (h i).isOpenMap) hT
  obtain ⟨x, ⟨hxU, hxV⟩, hxS, hxT⟩ :=
    (dense_of_mem_residual (inter_mem hS hpre)).inter_open_nonempty
      (U ∩ h i ⁻¹' V) (hU.inter (hV.preimage (h i).continuous)) hi
  exact hTA ⟨hxV, hxT⟩ ((hinv i x).mp (hSA ⟨hxU, hxS⟩))

end HewittSavage


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
