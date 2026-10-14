/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Defs
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Separation.Regular

/-!
# Countable open-cover refinements

The precise indexed refinement property is derived from the ordinary cover
definition; its index set is not imposed on the original refinement.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X : Type*} [TopologicalSpace X]

/-- Regrouping a locally finite family by any map preserves local finiteness. -/
theorem locallyFinite_group {ι κ : Type*} {V : ι → Set X}
    (hV : LocallyFinite V) (a : ι → κ) :
    LocallyFinite (fun k => ⋃ i, ⋃ (_ : a i = k), V i) := by
  intro x
  obtain ⟨t, ht, hfin⟩ := hV x
  refine ⟨t, ht, (hfin.image a).subset ?_⟩
  rintro k ⟨y, hy, hyt⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨hik, hyi⟩ := mem_iUnion.mp hi
  exact ⟨i, ⟨y, hyi, hyt⟩, hik⟩

/-- A countable indexed open cover admits a locally finite precise refinement. -/
theorem CountablyParacompact.precise_refinement (hX : CountablyParacompact X)
    {ι : Type*} [Countable ι] (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hU : ⋃ i, U i = univ) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ ⋃ i, V i = univ ∧
      LocallyFinite V ∧ ∀ i, V i ⊆ U i := by
  classical
  obtain ⟨V, hVo, hVU, hVf, hVUsub⟩ := hX (range U) (countable_range U)
    (by rintro s ⟨i, rfl⟩; exact ho i) (by simpa only [sUnion_range] using hU)
  have ha : ∀ s : V, ∃ i, (s : Set X) ⊆ U i := by
    intro s
    obtain ⟨t, ⟨i, rfl⟩, hst⟩ := hVUsub s s.property
    exact ⟨i, hst⟩
  choose a ha using ha
  let W : ι → Set X := fun i => ⋃ s : V, ⋃ (_ : a s = i), (s : Set X)
  refine ⟨W, ?_, ?_, locallyFinite_group hVf a, ?_⟩
  · intro i
    exact isOpen_iUnion fun s => isOpen_iUnion fun _ => hVo s s.property
  · apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ V := hVU.symm ▸ mem_univ x
    obtain ⟨s, hsV, hxs⟩ := mem_sUnion.mp hx
    exact mem_iUnion.mpr ⟨a ⟨s, hsV⟩,
      mem_iUnion.mpr ⟨⟨s, hsV⟩, mem_iUnion.mpr ⟨rfl, hxs⟩⟩⟩
  · intro i x hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    obtain ⟨hsi, hxs⟩ := mem_iUnion.mp hs
    exact hsi ▸ ha s hxs

/-- The natural-number precise-refinement formulation is equivalent to the
ordinary countable-cover definition, including finite and empty covers. -/
theorem countablyParacompact_iff_nat_precise : CountablyParacompact X ↔
    ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → (⋃ n, U n = univ) →
      ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ ⋃ n, V n = univ ∧
        LocallyFinite V ∧ ∀ n, V n ⊆ U n := by
  constructor
  · intro h U ho hU
    exact h.precise_refinement U ho hU
  · intro h U hc ho hU
    by_cases hn : U.Nonempty
    · obtain ⟨u, rfl⟩ := hc.exists_eq_range hn
      obtain ⟨v, hvo, hvU, hvf, hvu⟩ := h u
        (fun n => ho _ (mem_range_self n)) (by simpa only [sUnion_range] using hU)
      refine ⟨range v, ?_, ?_, hvf.on_range, ?_⟩
      · rintro s ⟨n, rfl⟩; exact hvo n
      · simpa only [sUnion_range] using hvU
      · rintro s ⟨n, rfl⟩
        exact ⟨u n, mem_range_self n, hvu n⟩
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hn
      refine ⟨∅, by simp, ?_, ?_, by simp⟩
      · simpa [he] using hU
      · intro x
        refine ⟨univ, univ_mem, ?_⟩
        have hem : {i : (∅ : Set (Set X)) | ((i : Set X) ∩ univ).Nonempty} = ∅ := by
          ext i
          exact False.elim i.property
        rw [hem]
        exact finite_empty

end Dowker
