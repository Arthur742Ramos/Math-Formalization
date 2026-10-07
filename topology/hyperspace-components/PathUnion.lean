/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Foundations
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.UnitInterval

@[expose] public section
open Set Topology TopologicalSpace

namespace HyperspaceComponents

variable {X : Type*} [tX : TopologicalSpace X]

/-- The union of the values of a hyperspace family over a parameter set. -/
def familyUnion (γ : unitInterval → NonemptyCompacts X) (s : Set unitInterval) : Set X :=
  ⋃ (t : unitInterval) (_ht : t ∈ s), (γ t : Set X)

theorem subset_familyUnion (γ : unitInterval → NonemptyCompacts X)
    {s : Set unitInterval} {t : unitInterval} (ht : t ∈ s) :
    (γ t : Set X) ⊆ familyUnion γ s := by
  intro x hx
  exact mem_iUnion₂.mpr ⟨t, ht, hx⟩

/-- Compact interval families of connected compact sets have continuum unions. -/
theorem subcontinuum_familyUnion_Icc (γ : unitInterval → NonemptyCompacts X)
    (hγ : Continuous γ) (hc : ∀ t, IsConnected (γ t : Set X))
    {a b : unitInterval} (hab : a ≤ b) :
    Composants.IsSubcontinuum (familyUnion γ (Icc a b)) := by
  let : TopologicalSpace (Set X) := .vietoris X
  constructor
  · simpa only [familyUnion, biUnion_image] using
      NonemptyCompacts.isCompact_biUnion_coe_of_isCompact (isCompact_Icc.image hγ)
  · refine ⟨(γ a).nonempty.mono (subset_familyUnion γ (left_mem_Icc.mpr hab)), ?_⟩
    exact vietoris.isPreconnected_biUnion isPreconnected_Icc
      (NonemptyCompacts.continuous_coe.comp hγ).continuousOn
      ⟨a, left_mem_Icc.mpr hab, (hc a).isPreconnected⟩

theorem familyUnion_Icc_split (γ : unitInterval → NonemptyCompacts X)
    {a b c : unitInterval} (hab : a ≤ b) (hbc : b ≤ c) :
    familyUnion γ (Icc a c) =
      familyUnion γ (Icc a b) ∪ familyUnion γ (Icc b c) := by
  ext x
  simp only [familyUnion, mem_iUnion, mem_Icc, mem_union]
  constructor
  · rintro ⟨t, ⟨hat, htc⟩, hx⟩
    rcases le_total t b with htb | hbt
    · exact Or.inl ⟨t, ⟨hat, htb⟩, hx⟩
    · exact Or.inr ⟨t, ⟨hbt, htc⟩, hx⟩
  · rintro (⟨t, ⟨hat, htb⟩, hx⟩ | ⟨t, ⟨hbt, htc⟩, hx⟩)
    · exact ⟨t, ⟨hat, htb.trans hbc⟩, hx⟩
    · exact ⟨t, ⟨hab.trans hbt, htc⟩, hx⟩

/-- A path through proper subcontinua of an indecomposable Hausdorff space
has a proper total union. The finite subdivision may have repeated vertices. -/
theorem proper_familyUnion [hT2 : T2Space X] (hi : Composants.IsIndecomposable X)
    (γ : unitInterval → NonemptyCompacts X) (hγ : Continuous γ)
    (hc : ∀ t, IsConnected (γ t : Set X))
    (hp : ∀ t, (γ t : Set X) ≠ univ) :
    Composants.IsSubcontinuum (familyUnion γ univ) ∧ familyUnion γ univ ≠ univ := by
  classical
  let U : X → Set unitInterval := fun x => {t | (γ t : Set X) ⊆ ({x} : Set X)ᶜ}
  have hU : ∀ x, IsOpen (U x) := fun x =>
    (NonemptyCompacts.isOpen_subsets_of_isOpen isClosed_singleton.isOpen_compl).preimage hγ
  have hcover : univ ⊆ ⋃ x, U x := by
    intro t _
    obtain ⟨x, hx⟩ : ∃ x : X, x ∉ (γ t : Set X) := by
      by_contra h
      apply hp t
      apply eq_univ_iff_forall.mpr
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exact mem_iUnion.mpr ⟨x, fun y hy hyx => hx (mem_singleton_iff.mp hyx ▸ hy)⟩
  obtain ⟨v, hv0, hvm, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU hcover
  have hseg : ∀ n, familyUnion γ (Icc (v n) (v (n + 1))) ≠ univ := by
    intro n
    obtain ⟨x, hx⟩ := hsub n
    intro he
    have hxmem : x ∈ familyUnion γ (Icc (v n) (v (n + 1))) := he ▸ mem_univ x
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxmem
    exact hx ht hxt (mem_singleton x)
  have hprefix : ∀ n, familyUnion γ (Icc 0 (v n)) ≠ univ := by
    intro n
    induction n with
    | zero => simpa [familyUnion, hv0] using hp 0
    | succ n ih =>
      have hleft := subcontinuum_familyUnion_Icc γ hγ hc
        (show (0 : unitInterval) ≤ v n from unitInterval.nonneg')
      have hright := subcontinuum_familyUnion_Icc γ hγ hc (hvm (Nat.le_succ n))
      rw [familyUnion_Icc_split γ (show (0 : unitInterval) ≤ v n from unitInterval.nonneg')
        (hvm (Nat.le_succ n))]
      intro he
      exact (hi _ _ hleft hright he).elim ih (hseg n)
  have hI : Icc (0 : unitInterval) 1 = univ := by
    ext t
    simp only [mem_Icc, mem_univ, iff_true]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩
  refine ⟨?_, ?_⟩
  · rw [← hI]
    exact subcontinuum_familyUnion_Icc γ hγ hc unitInterval.nonneg'
  · simpa only [hm m le_rfl, hI] using hprefix m

end HyperspaceComponents

#print axioms HyperspaceComponents.proper_familyUnion
