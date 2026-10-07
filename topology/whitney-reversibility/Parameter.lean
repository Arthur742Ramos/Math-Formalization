/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Chain

@[expose] public section

open Set Topology TopologicalSpace

namespace OrderArcs

/-- Parametrization of a compact order by a continuous strictly increasing scalar. -/
theorem exists_order_arc_in_order {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [PartialOrder Y] [T2Space Y] (hclosed : IsClosed {p : Y × Y | p.1 ≤ p.2})
    (f : Y → ℝ) (hfc : Continuous f) (hfs : StrictMono f)
    (hbetween : ∀ x y : Y, x < y → ∃ z : Y, x < z ∧ z < y)
    (a b : Y) (hab : a < b) (ha : ∀ x : Y, a ≤ x) (hb : ∀ x : Y, x ≤ b) :
    ∃ γ : unitInterval → Y, Continuous γ ∧ IsEmbedding γ ∧ γ 0 = a ∧ γ 1 = b ∧ StrictMono γ := by
  classical
  obtain ⟨M, hMc, hM, hMa, hMb, hinj, himage⟩ :=
    exists_compact_chain_image hclosed f hfc hfs hbetween a b hab ha hb
  have : CompactSpace M := isCompact_iff_compactSpace.mp hMc
  let g : M → Icc (f a) (f b) := fun x => ⟨f x, himage ▸ ⟨x, x.property, rfl⟩⟩
  have hgc : Continuous g := (hfc.comp continuous_subtype_val).subtype_mk _
  have hgb : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hinj x.property y.property (congrArg Subtype.val hxy)
    · intro y
      have hy : y.val ∈ f '' M := himage.symm ▸ y.property
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      exact hxy
  let e : M ≃ Icc (f a) (f b) := Equiv.ofBijective g hgb
  let E : M ≃ₜ Icc (f a) (f b) :=
    Continuous.homeoOfEquivCompactToT2 (show Continuous e from hgc)
  let H : unitInterval ≃ₜ M := (iccHomeoI (f a) (f b) (hfs hab)).symm.trans E.symm
  let γ : unitInterval → Y := fun t => (H t).val
  have hvalue : ∀ t : unitInterval, f (γ t) = (f b - f a) * (t : ℝ) + f a := by
    intro t
    have heq : E (H t) = (iccHomeoI (f a) (f b) (hfs hab)).symm t :=
      E.apply_symm_apply _
    have h := congrArg Subtype.val heq
    exact h
  have hzero : γ 0 = a := hinj (H 0).property hMa (by simpa using hvalue 0)
  have hone : γ 1 = b := hinj (H 1).property hMb (by simpa using hvalue 1)
  have hmono : StrictMono γ := by
    intro s t hst
    have hfstrict : f (γ s) < f (γ t) := by
      rw [hvalue, hvalue]
      have hst' : (s : ℝ) < (t : ℝ) := hst
      simpa only [add_comm] using add_lt_add_right
        (mul_lt_mul_of_pos_left hst' (sub_pos.mpr (hfs hab))) (f a)
    rcases hM.total (H s).property (H t).property with hle | hle
    · refine lt_of_le_of_ne hle ?_
      intro heq
      exact (ne_of_lt hfstrict) (congrArg f heq)
    · exact False.elim ((not_lt_of_ge (hfs.monotone hle)) hfstrict)
  exact ⟨γ, continuous_subtype_val.comp H.continuous,
    IsEmbedding.subtypeVal.comp H.isEmbedding, hzero, hone, hmono⟩

end OrderArcs

#print axioms OrderArcs.exists_order_arc_in_order
