/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Checkpoint
public import Mathlib.Order.Zorn

@[expose] public section

open Set Topology TopologicalSpace

namespace OrderArcs

/-- Connected compact sets form a closed part of the Vietoris hyperspace. -/
theorem isClosed_connected_values {X : Type*} [TopologicalSpace X] [T2Space X] :
    IsClosed {K : NonemptyCompacts X | IsConnected (K : Set X)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro K hK
  have hn : ¬ IsPreconnected (K : Set X) := fun h => hK ⟨K.nonempty, h⟩
  rw [isPreconnected_closed_iff] at hn
  push Not at hn
  obtain ⟨F, G, hF, hG, hKFG, hKF, hKG, hmiss⟩ := hn
  have hdis : Disjoint ((K : Set X) ∩ F) ((K : Set X) ∩ G) := by
    rw [disjoint_left]
    intro x hx hy
    have hx' : x ∈ (K : Set X) ∩ (F ∩ G) := ⟨hx.1, hx.2, hy.2⟩
    rw [hmiss] at hx'
    exact hx'
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (K.isCompact.inter_right hF)
      (K.isCompact.inter_right hG) hdis
  let N : Set (NonemptyCompacts X) :=
    {L | (L : Set X) ⊆ U ∪ V} ∩
      {L | ((L : Set X) ∩ U).Nonempty} ∩ {L | ((L : Set X) ∩ V).Nonempty}
  have hN : IsOpen N :=
    ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV)
  have hKN : K ∈ N := by
    refine ⟨⟨?_, hKF.mono ?_⟩, hKG.mono ?_⟩
    · intro x hx
      exact (hKFG hx).elim (fun h => Or.inl (hKU ⟨hx, h⟩))
        (fun h => Or.inr (hKV ⟨hx, h⟩))
    · intro x hx
      exact ⟨hx.1, hKU hx⟩
    · intro x hx
      exact ⟨hx.1, hKV hx⟩
  refine Filter.mem_of_superset (hN.mem_nhds hKN) ?_
  intro L hLN hLc
  obtain ⟨x, hxL, hxUV⟩ := hLc.isPreconnected U V hU hV hLN.1.1 hLN.1.2 hLN.2
  exact Set.disjoint_left.mp hUV hxUV.1 hxUV.2

/-- Inclusion is closed in the hyperspace product. -/
theorem isClosed_inclusion {X : Type*} [TopologicalSpace X] [T2Space X] :
    IsClosed {p : NonemptyCompacts X × NonemptyCompacts X | p.1 ≤ p.2} := by
  simpa only [sup_eq_right] using
    (isClosed_eq (continuous_fst.sup continuous_snd) continuous_snd :
      IsClosed {p : NonemptyCompacts X × NonemptyCompacts X | p.1 ⊔ p.2 = p.2})

/-- Taking closure preserves an inclusion chain. -/
theorem isChain_closure {Y : Type*} [TopologicalSpace Y] [Preorder Y]
    (hclosed : IsClosed {p : Y × Y | p.1 ≤ p.2}) {M : Set Y}
    (hM : IsChain (· ≤ ·) M) : IsChain (· ≤ ·) (closure M) := by
  have hcomp : IsClosed {p : Y × Y | p.1 ≤ p.2 ∨ p.2 ≤ p.1} :=
    hclosed.union (hclosed.preimage continuous_swap)
  have hsub : M ×ˢ M ⊆ {p : Y × Y | p.1 ≤ p.2 ∨ p.2 ≤ p.1} := by
    intro p hp
    exact hM.total hp.1 hp.2
  have hcl := closure_minimal hsub hcomp
  rw [closure_prod_eq] at hcl
  intro x hx y hy _
  have hxy : (x, y) ∈ closure M ×ˢ closure M := ⟨hx, hy⟩
  exact hcl hxy

end OrderArcs

#print axioms OrderArcs.isClosed_connected_values
#print axioms OrderArcs.isClosed_inclusion
#print axioms OrderArcs.isChain_closure
