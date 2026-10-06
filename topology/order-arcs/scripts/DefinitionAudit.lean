module
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.UnitInterval
open Set Topology TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X]
example (s : Set X) : IsPreconnected s ↔
    ∀ U V : Set X, IsOpen U → IsOpen V → s ⊆ U ∪ V →
      (s ∩ U).Nonempty → (s ∩ V).Nonempty → (s ∩ (U ∩ V)).Nonempty := Iff.rfl
example (s : Set X) : IsConnected s ↔ s.Nonempty ∧ IsPreconnected s := Iff.rfl
example : CompactSpace X ↔ IsCompact (univ : Set X) :=
  ⟨fun h => h.isCompact_univ, fun h => ⟨h⟩⟩
example (s : Set X) : IsCompact s ↔
    ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i := isCompact_iff_finite_subcover
example (K : NonemptyCompacts X) : (K : Set X).Nonempty := K.nonempty
example (K : NonemptyCompacts X) : IsCompact (K : Set X) := K.isCompact
example (A B : NonemptyCompacts X) : A ≤ B ↔ (A : Set X) ⊆ (B : Set X) := Iff.rfl
example (A B : NonemptyCompacts X) : A < B ↔ (A : Set X) ⊂ (B : Set X) := Iff.rfl
example : unitInterval = Icc (0 : ℝ) 1 := rfl
example {Y : Type v} [Preorder Y] (γ : unitInterval → Y) :
    StrictMono γ ↔ ∀ ⦃s t : unitInterval⦄, s < t → γ s < γ t := Iff.rfl
example (C : Set X) : (inferInstance : TopologicalSpace C) =
    TopologicalSpace.induced ((↑) : C → X) inferInstance := rfl
