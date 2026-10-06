module
public import Solution
open Set Composants
universe u
variable {X : Type u} [TopologicalSpace X]

example (K : Set X) : IsSubcontinuum K ↔ IsCompact K ∧ IsConnected K := Iff.rfl
example : IsIndecomposable X ↔
    ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L → K ∪ L = univ → K = univ ∨ L = univ := Iff.rfl
example (x y : X) : y ∈ composant x ↔
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K := by
  simp only [composant, IsSubcontinuum, mem_ofPred_eq, and_assoc]

-- The literal union has no proper nonempty subcontinuum in a singleton space.
example [Subsingleton X] (x : X) : composant x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨K, hK, hp, hx, _⟩
  apply hp
  ext z
  simp only [mem_univ, iff_true]
  exact (Subsingleton.elim x z) ▸ hx
example : ¬ Dense (∅ : Set Unit) := by
  intro h
  have := h ()
  simp at this
example : ¬ IsConnected (∅ : Set Unit) := fun h => h.nonempty.ne_empty rfl

-- Relative density uses the actual induced topology of a subcontinuum.
example [T2Space X] (C : Set X) (hc : IsCompact C) (hn : IsConnected C)
    [Nontrivial C] (x : C) : Dense (composant x) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hc
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp hn
  exact dense_composant x
#print axioms Composants.mem_composant_self
#print axioms Composants.dense_composant
#print axioms Composants.isConnected_composant
#print axioms Composants.composants_eq_or_disjoint
#print axioms Composants.iUnion_composant
#print axioms Composants.composant_countable_union
#print axioms Composants.isMeagre_composant
#print axioms Composants.uncountably_many_composants
#print axioms Composants.IsSubcontinuum
#print axioms Composants.IsIndecomposable
#print axioms Composants.composant
