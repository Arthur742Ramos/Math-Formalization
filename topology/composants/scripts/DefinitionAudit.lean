module
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Literal and semantic checks against the actual pinned dependencies. -/
open Set
universe u
variable {X : Type u} [tX : TopologicalSpace X]

example (s : Set X) : IsPreconnected s ↔
    ∀ U V : Set X, IsOpen U → IsOpen V → s ⊆ U ∪ V →
      (s ∩ U).Nonempty → (s ∩ V).Nonempty → (s ∩ (U ∩ V)).Nonempty := Iff.rfl
example (s : Set X) : IsConnected s ↔ s.Nonempty ∧ IsPreconnected s := Iff.rfl
example (s : Set X) : IsClosed s ↔ IsOpen sᶜ :=
  ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩
example (s : Set X) : interior s = ⋃₀ {t : Set X | IsOpen t ∧ t ⊆ s} := rfl
example (s : Set X) : closure s = ⋂₀ {t : Set X | IsClosed t ∧ s ⊆ t} := rfl
example (s : Set X) : IsNowhereDense s ↔ interior (closure s) = ∅ := Iff.rfl
example : CompactSpace X ↔ IsCompact (univ : Set X) :=
  ⟨fun h => h.isCompact_univ, fun h => ⟨h⟩⟩
example (s : Set X) : IsCompact s ↔
    ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  isCompact_iff_finite_subcover
example : T2Space X ↔ ∀ ⦃x y : X⦄, x ≠ y →
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V :=
  ⟨fun h => h.t2, fun h => ⟨h⟩⟩
example : PreconnectedSpace X ↔ IsPreconnected (univ : Set X) :=
  ⟨fun h => h.isPreconnected_univ, fun h => ⟨h⟩⟩
example : ConnectedSpace X ↔ IsConnected (univ : Set X) :=
  ⟨fun h => @isConnected_univ X tX h, fun h =>
    { isPreconnected_univ := h.isPreconnected, toNonempty := ⟨h.nonempty.choose⟩ }⟩
example : Nontrivial X ↔ ∃ x y : X, x ≠ y := nontrivial_iff
example (C : Set X) : (inferInstance : TopologicalSpace C) =
    TopologicalSpace.induced ((↑) : C → X) tX := rfl
example (C : Set X) (U : Set C) : IsOpen U ↔
    ∃ V : Set X, IsOpen V ∧ ((↑) : C → X) ⁻¹' V = U := Iff.rfl
example (s : Set X) : Dense s ↔ ∀ x, x ∈ closure s := Iff.rfl
example (s : Set X) : IsMeagre s ↔ sᶜ ∈ residual X := Iff.rfl
example (s : Set X) : s.Countable ↔ Countable s := Iff.rfl
example : SecondCountableTopology X ↔ ∃ b : Set (Set X),
    b.Countable ∧ tX = TopologicalSpace.generateFrom b :=
  ⟨fun h => h.is_open_generated_countable, fun h => ⟨h⟩⟩
example : BaireSpace X ↔ ∀ f : ℕ → Set X,
    (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n) :=
  ⟨fun h => h.baire_property, fun h => ⟨h⟩⟩
