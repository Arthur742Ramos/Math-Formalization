/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the root LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Material Lean proof authorship: OpenAI Codex. Classical source:
Kucharski–Plewik, arXiv:math/0605469v1, introduction, printed pp.1–2.
-/
module

public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Bases

public section

open Set Filter Topology TopologicalSpace

namespace KuratowskiUlam

/-- A countable π-base consists of nonempty open sets refining every nonempty open set.
The family may be empty, which includes the empty space. -/
@[expose] def IsCountablePiBase {Y : Type*} [TopologicalSpace Y]
    (B : Set (Set Y)) : Prop :=
  B.Countable ∧ (∀ V ∈ B, IsOpen V ∧ V.Nonempty) ∧
    ∀ W : Set Y, IsOpen W → W.Nonempty → ∃ V ∈ B, V ⊆ W

/-- Countable π-weight; no separation or nonempty-space assumption is built in. -/
@[expose] def HasCountablePiBase (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∃ B : Set (Set Y), IsCountablePiBase B

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every second-countable space has a countable π-base. -/
theorem hasCountablePiBase_of_secondCountable [SecondCountableTopology Y] :
    HasCountablePiBase Y := by
  refine ⟨countableBasis Y, countable_countableBasis Y, ?_, ?_⟩
  · exact fun V hV => ⟨isOpen_of_mem_countableBasis hV,
      nonempty_of_mem_countableBasis hV⟩
  · intro W hW ⟨y, hy⟩
    obtain ⟨V, hV, _, hVW⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hy hW
    exact ⟨V, hV, hVW⟩

/-- A dense open subset of a product has dense sections outside a meagre exceptional set. -/
theorem eventually_dense_sections (hY : HasCountablePiBase Y) {U : Set (X × Y)}
    (hU : IsOpen U) (hd : Dense U) :
    ∀ᶠ x in residual X, Dense (Prod.mk x ⁻¹' U) := by
  obtain ⟨B, hBc, hBo, hB⟩ := hY
  let G : Set Y → Set X := fun V => Prod.fst '' (U ∩ (univ ×ˢ V))
  have hG : ∀ V ∈ B, G V ∈ residual X := by
    intro V hV
    refine residual_of_dense_open
      (isOpenMap_fst _ (hU.inter (isOpen_univ.prod (hBo V hV).1))) ?_
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ :=
      hd.inter_open_nonempty (W ×ˢ V) (hW.prod (hBo V hV).1)
        (hWne.prod (hBo V hV).2)
    exact ⟨x, hx, (x, y), ⟨hxy, trivial, hy⟩, rfl⟩
  filter_upwards [(eventually_countable_ball hBc).mpr hG] with x hx
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨V, hVB, hVW⟩ := hB W hW hWne
  obtain ⟨⟨x', y⟩, ⟨hxy, _, hy⟩, heq⟩ := hx V hVB
  change x' = x at heq
  subst x'
  exact ⟨y, hVW hy, hxy⟩

/-- The nowhere-dense Kuratowski–Ulam theorem, with arbitrary first factor. -/
theorem eventually_isNowhereDense_sections (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : IsNowhereDense A) :
    ∀ᶠ x in residual X, IsNowhereDense (Prod.mk x ⁻¹' A) := by
  have hc := isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure, hA.closure⟩
  filter_upwards [eventually_dense_sections hY hc.1 hc.2] with x hx
  have hcl : IsClosed (Prod.mk x ⁻¹' closure A) :=
    isClosed_closure.preimage (continuous_const.prodMk continuous_id)
  have hn : IsNowhereDense (Prod.mk x ⁻¹' closure A) :=
    (isClosed_isNowhereDense_iff_compl.mpr ⟨hcl.isOpen_compl, hx⟩).2
  exact hn.mono (preimage_mono subset_closure)

/-- The category analogue of the forward Fubini theorem: residual sets have residual sections. -/
theorem eventually_residual_sections (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : A ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y := by
  obtain ⟨S, hSo, hSd, hSc, hSA⟩ := mem_residual_iff.mp hA
  have hgood : ∀ U ∈ S, ∀ᶠ x in residual X, Prod.mk x ⁻¹' U ∈ residual Y := by
    intro U hU
    filter_upwards [eventually_dense_sections hY (hSo U hU) (hSd U hU)] with x hx
    exact residual_of_dense_open
      ((hSo U hU).preimage (continuous_const.prodMk continuous_id)) hx
  filter_upwards [(eventually_countable_ball hSc).mpr hgood] with x hx
  have hi : (⋂ U ∈ S, Prod.mk x ⁻¹' U) ∈ residual Y :=
    (countable_bInter_mem hSc).mpr hx
  apply mem_of_superset hi
  intro y hy
  apply hSA
  exact fun U hU => mem_iInter₂.mp hy U hU

/-- Meagre subsets have meagre sections for residually many parameters, without Baire hypotheses. -/
theorem eventually_isMeagre_sections (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : IsMeagre A) :
    ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' A) :=
  eventually_residual_sections hY hA

/-- For sets with the property of Baire, generic meagreness of sections detects meagreness.
The Baire hypotheses belong to this converse, not to the forward section theorem. -/
theorem isMeagre_iff_eventually_sections [BaireSpace X] [BaireSpace Y]
    (hY : HasCountablePiBase Y) {A : Set (X × Y)} (hA : BaireMeasurableSet A) :
    IsMeagre A ↔ ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' A) := by
  refine ⟨eventually_isMeagre_sections hY, ?_⟩
  intro hsections
  obtain ⟨O, hO, hAO⟩ := hA.residualEq_isOpen
  let E : Set (X × Y) := {z | ¬ (z ∈ A ↔ z ∈ O)}
  have hE : IsMeagre E := by
    change ∀ᶠ z in residual (X × Y), ¬¬ (z ∈ A ↔ z ∈ O)
    exact hAO.mem_iff.mono (fun _ hz => not_not.mpr hz)
  have hgood : ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' O) := by
    filter_upwards [hsections, eventually_isMeagre_sections hY hE] with x hx hEx
    apply (hx.union hEx).mono
    intro y hy
    by_cases ha : (x, y) ∈ A
    · exact Or.inl ha
    · exact Or.inr (fun hiff => ha (hiff.mpr hy))
  have hOempty : O = ∅ := by
    by_contra hne
    obtain ⟨⟨x₀, y₀⟩, hxy⟩ := nonempty_iff_ne_empty.mpr hne
    obtain ⟨U, V, hU, hV, hx₀, hy₀, hUV⟩ := isOpen_prod_iff.mp hO x₀ y₀ hxy
    obtain ⟨x, hxgood, hxU⟩ := (dense_of_mem_residual hgood).exists_mem_open hU ⟨x₀, hx₀⟩
    exact not_isMeagre_of_isOpen hV ⟨y₀, hy₀⟩
      (hxgood.mono (fun y hy => hUV ⟨hxU, hy⟩))
  change ∀ᶠ z in residual (X × Y), z ∉ A
  filter_upwards [hAO.mem_iff] with z hz
  simpa only [hOempty, mem_empty_iff_false, iff_false] using hz

/-- The comeagre form of category Fubini for sets with the property of Baire. -/
theorem residual_iff_eventually_sections [BaireSpace X] [BaireSpace Y]
    (hY : HasCountablePiBase Y) {A : Set (X × Y)} (hA : BaireMeasurableSet A) :
    A ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y := by
  simpa only [IsMeagre, compl_compl, preimage_compl] using
    isMeagre_iff_eventually_sections hY hA.compl

/-- A Baire space times a Baire space of countable π-weight is Baire.
No separation, completeness, countable basis or nonemptiness is assumed. -/
theorem baireSpace_prod [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y) :
    BaireSpace (X × Y) := by
  constructor
  intro U ho hd
  have hres : (⋂ n, U n) ∈ residual (X × Y) :=
    countable_iInter_mem.mpr (fun n => residual_of_dense_open (ho n) (hd n))
  have hgood := eventually_residual_sections hY hres
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨⟨x₀, y₀⟩, hxy⟩ := hWne
  obtain ⟨V, T, hV, hT, hx₀, hy₀, hVT⟩ := isOpen_prod_iff.mp hW x₀ y₀ hxy
  obtain ⟨x, hxgood, hxV⟩ := (dense_of_mem_residual hgood).exists_mem_open hV ⟨x₀, hx₀⟩
  obtain ⟨y, hygood, hyT⟩ := (dense_of_mem_residual hxgood).exists_mem_open hT ⟨y₀, hy₀⟩
  exact ⟨(x, y), hVT ⟨hxV, hyT⟩, hygood⟩

end KuratowskiUlam
