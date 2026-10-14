/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Covers
public import Mathlib.Topology.ShrinkingLemma

/-!
# The decreasing closed sequence characterization

This is Dowker's Theorem 2(d), proved equivalent to the independent ordinary
cover definition in normal spaces.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Open expansions with empty intersection for decreasing closed sequences. -/
def ClosedSequenceProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ F : ℕ → Set X, (∀ n, IsClosed (F n)) → Antitone F → (⋂ n, F n) = ∅ →
    ∃ G : ℕ → Set X, (∀ n, IsOpen (G n)) ∧ (∀ n, F n ⊆ G n) ∧ (⋂ n, G n) = ∅

theorem CountablyParacompact.closed_sequence_property [NormalSpace X]
    (hX : CountablyParacompact X) : ClosedSequenceProperty X := by
  intro F hFc _ hFe
  have hcov : (⋃ n, (F n)ᶜ) = univ := by
    rw [← compl_iInter, hFe, compl_empty]
  obtain ⟨V, hVo, hVU, hVf, hVF⟩ :=
    hX.precise_refinement (fun n => (F n)ᶜ) (fun n => (hFc n).isOpen_compl) hcov
  obtain ⟨W, hWU, _, hWV⟩ :=
    exists_iUnion_eq_closure_subset hVo (hVf.point_finite) hVU
  refine ⟨fun n => (closure (W n))ᶜ, (fun _ => isClosed_closure.isOpen_compl), ?_, ?_⟩
  · intro n x hx hxc
    exact hVF n (hWV n hxc) hx
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxW : x ∈ ⋃ n, W n := hWU.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxW
    exact (mem_iInter.mp hx n) (subset_closure hn)

theorem countablyParacompact_of_closed_sequence_property [NormalSpace X]
    (hX : ClosedSequenceProperty X) : CountablyParacompact X := by
  apply countablyParacompact_iff_nat_precise.mpr
  intro U hUo hUU
  classical
  let F : ℕ → Set X := fun n => ⋂ k, ⋂ (_ : k ≤ n), (U k)ᶜ
  have hFc : ∀ n, IsClosed (F n) := fun n =>
    isClosed_iInter fun k => isClosed_iInter fun _ => (hUo k).isClosed_compl
  have hFa : Antitone F := by
    intro n m hnm x hx
    exact mem_iInter₂.mpr fun k hkn => mem_iInter₂.mp hx k (hkn.trans hnm)
  have hFe : (⋂ n, F n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxU : x ∈ ⋃ n, U n := hUU.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact mem_iInter₂.mp (mem_iInter.mp hx n) n le_rfl hn
  obtain ⟨G, hGo, hFG, hGe⟩ := hX F hFc hFa hFe
  choose O hOo hFO hOG using fun n => normal_exists_closure_subset (hFc n) (hGo n) (hFG n)
  let V : ℕ → Set X := fun n => U n ∩ ⋂ j : Fin n, O j
  refine ⟨V, (fun n => (hUo n).inter (isOpen_iInter_of_finite fun j => hOo j)), ?_, ?_,
    (fun _ => inter_subset_left)⟩
  · apply eq_univ_of_forall
    intro x
    have hxU : ∃ n, x ∈ U n := mem_iUnion.mp (hUU.symm ▸ mem_univ x)
    let m := Nat.find hxU
    refine mem_iUnion.mpr ⟨m, Nat.find_spec hxU, mem_iInter.mpr ?_⟩
    intro j
    apply hFO j
    refine mem_iInter₂.mpr fun k hkj => ?_
    exact Nat.find_min hxU (lt_of_le_of_lt hkj j.isLt)
  · intro x
    have hxG : ∃ n, x ∉ G n := by
      by_contra! hn
      have : x ∈ ⋂ n, G n := mem_iInter.mpr hn
      rw [hGe] at this
      exact this
    obtain ⟨n, hn⟩ := hxG
    have hxn : x ∈ (closure (O n))ᶜ := fun hx => hn (hOG n hx)
    refine ⟨(closure (O n))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxn,
      (finite_Iic n).subset ?_⟩
    intro m hm
    change m ≤ n
    by_contra! hnm
    obtain ⟨y, hyV, hyO⟩ := hm
    exact hyO (subset_closure (mem_iInter.mp hyV.2 ⟨n, hnm⟩))

theorem countablyParacompact_iff_closed_sequence_property [NormalSpace X] :
    CountablyParacompact X ↔ ClosedSequenceProperty X :=
  ⟨CountablyParacompact.closed_sequence_property,
    countablyParacompact_of_closed_sequence_property⟩

end Dowker
