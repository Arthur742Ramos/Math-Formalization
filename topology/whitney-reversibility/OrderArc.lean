/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Parameter

@[expose] public section

open Set Topology TopologicalSpace

namespace OrderArcs

/-- Nonempty compact connected sets between two specified endpoints. -/
abbrev ContinuumInterval {X : Type*} [tX : TopologicalSpace X] (A B : NonemptyCompacts X) :=
  {K : NonemptyCompacts X // A ≤ K ∧ K ≤ B ∧ IsConnected (K : Set X)}

/-- An order arc between properly nested subcontinua of a compact metric space.
The ambient space itself need not be connected. -/
theorem exists_order_arc {X : Type*} [mX : MetricSpace X] [cX : CompactSpace X]
    (A B : NonemptyCompacts X) (hA : IsConnected (A : Set X))
    (hB : IsConnected (B : Set X)) (hAB : A < B) :
    ∃ γ : unitInterval → NonemptyCompacts X,
      Continuous γ ∧ IsEmbedding γ ∧ γ 0 = A ∧ γ 1 = B ∧
      (∀ t : unitInterval, IsConnected (γ t : Set X)) ∧ StrictMono γ := by
  classical
  have : Nonempty X := A.nonempty.to_subtype.map Subtype.val
  obtain ⟨q, hq⟩ := exists_dense_seq X
  let P := ContinuumInterval A B
  have hPclosed : IsClosed {K : NonemptyCompacts X | A ≤ K ∧ K ≤ B ∧ IsConnected (K : Set X)} :=
    (isClosed_inclusion.preimage (continuous_const.prodMk continuous_id)).inter
      ((isClosed_inclusion.preimage (continuous_id.prodMk continuous_const)).inter
        isClosed_connected_values)
  have : CompactSpace P := isCompact_iff_compactSpace.mp hPclosed.isCompact
  let a : P := ⟨A, le_rfl, hAB.le, hA⟩
  let b : P := ⟨B, hAB.le, le_rfl, hB⟩
  have hclosed : IsClosed {p : P × P | p.1 ≤ p.2} :=
    isClosed_inclusion.preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  let f : P → ℝ := fun K => height q K.val
  have hfc : Continuous f := (continuous_height q).comp continuous_subtype_val
  have hfs : StrictMono f := fun _ _ h => strictMono_height q hq h
  have hbetween : ∀ K L : P, K < L → ∃ D : P, K < D ∧ D < L := by
    intro K L hKL
    obtain ⟨D, hDc, hD, hKD, hDL⟩ := exists_intermediate
      K.val.isCompact K.property.2.2 L.val.isCompact L.property.2.2 hKL
    let d : NonemptyCompacts X := ⟨⟨D, hDc⟩, hD.nonempty⟩
    let d' : P := ⟨d, K.property.1.trans hKD.subset,
      hDL.subset.trans L.property.2.1, hD⟩
    exact ⟨d', hKD, hDL⟩
  obtain ⟨γ, hγ, hγemb, hγ0, hγ1, hγmono⟩ := exists_order_arc_in_order
    hclosed f hfc hfs hbetween a b hAB (fun K => K.property.1) (fun K => K.property.2.1)
  refine ⟨fun t => (γ t).val, continuous_subtype_val.comp hγ,
    IsEmbedding.subtypeVal.comp hγemb, ?_, ?_, fun t => (γ t).property.2.2, ?_⟩
  · exact congrArg Subtype.val hγ0
  · exact congrArg Subtype.val hγ1
  · exact hγmono

end OrderArcs

#print axioms OrderArcs.exists_order_arc
