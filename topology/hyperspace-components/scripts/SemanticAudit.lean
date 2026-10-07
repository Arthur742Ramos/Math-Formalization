module
public import Solution
@[expose] public section
open Set Topology TopologicalSpace

example {X : Type*} [TopologicalSpace X] (K : Set X) :
  Composants.IsSubcontinuum K ↔ IsCompact K ∧ IsConnected K := Iff.rfl

example {X : Type*} [TopologicalSpace X] :
  Composants.IsIndecomposable X ↔ (∀ K L : Set X, (IsCompact K ∧ IsConnected K) → (IsCompact L ∧ IsConnected L) → K ∪ L = univ → K = univ ∨ L = univ) := Iff.rfl

example {X : Type*} [TopologicalSpace X] (x : X) :
  Composants.composant x = {y | ∃ K : Set X, (IsCompact K ∧ IsConnected K) ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K} := rfl

example {X : Type*} [TopologicalSpace X] (γ : unitInterval → NonemptyCompacts X) (s : Set unitInterval) :
  HyperspaceComponents.familyUnion γ s = ⋃ t ∈ s, (γ t : Set X) := rfl

example {X : Type*} [TopologicalSpace X] :
  HyperspaceComponents.ProperContinuum X = {K : NonemptyCompacts X // IsConnected (K : Set X) ∧ (K : Set X) ≠ univ} := rfl

example {X : Type*} [TopologicalSpace X] [Subsingleton X] :
  IsEmpty (HyperspaceComponents.ProperContinuum X) := HyperspaceComponents.no_proper_continuum_of_subsingleton

#print axioms HyperspaceComponents.proper_familyUnion
#print axioms HyperspaceComponents.joined_iff_common_continuum
#print axioms HyperspaceComponents.joined_iff_same_composant
#print axioms HyperspaceComponents.pathComponent_eq_composant
#print axioms HyperspaceComponents.uncountably_many_path_components
#print axioms HyperspaceComponents.no_proper_continuum_of_subsingleton
#print axioms Composants.IsSubcontinuum
#print axioms Composants.IsIndecomposable
#print axioms Composants.composant
#print axioms HyperspaceComponents.familyUnion
#print axioms HyperspaceComponents.ProperContinuum
#print axioms HyperspaceComponents.proper_union
#print axioms HyperspaceComponents.exists_common_continuum_of_composant
#print axioms HyperspaceComponents.joined_of_le
#print axioms HyperspaceComponents.singletonContinuum
#print axioms HyperspaceComponents.composant_eq_of_singleton_components_eq
#print axioms OrderArcs.exists_order_arc
#print axioms Composants.uncountably_many_composants
#print axioms BoundaryBumping.closed_component_meets_frontier
