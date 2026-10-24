module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic

@[expose] public section
open Set Filter
open scoped Topology
namespace EZero

/-- Adapted from the credited campaign category helper. The open approximation has a nonempty region when the Baire set is nonmeagre. -/
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

end EZero
