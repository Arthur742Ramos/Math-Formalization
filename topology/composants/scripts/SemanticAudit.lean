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

-- Cover membership, separation, and refinement are literal set predicates.
example (ω : Set (Set X)) : IsOpenCover ω ↔
    (∀ U ∈ ω, IsOpen U) ∧ ⋃₀ ω = univ := Iff.rfl
example (P A B : Set X) : IsPartitionBetween P A B ↔
    IsClosed P ∧ ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = Pᶜ ∧ A ⊆ U ∧ B ⊆ V := Iff.rfl
universe v
example {Y : Type v} [TopologicalSpace Y] (ω : Set (Set X)) {P : Set X} (f : P → Y) :
    IsOmegaMap ω f ↔ Continuous f ∧ ∃ γ : Set (Set Y), IsOpenCover γ ∧
      ∀ V ∈ γ, ∃ U ∈ ω, f ⁻¹' V ⊆ Subtype.val ⁻¹' U := Iff.rfl
example (Y : Type v) [TopologicalSpace Y] : IsContinuum Y ↔
    Nonempty Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧ T2Space Y := Iff.rfl
example : ¬ IsOpenCover (∅ : Set (Set Unit)) := by
  intro h
  have hh := congrArg (fun s : Set Unit => () ∈ s) h.2
  simp at hh
-- The massive disjoint-set hypotheses are impossible on a singleton continuum.
example [Subsingleton X] (A B : Set X) (hd : Disjoint A B)
    (ha : (interior A).Nonempty) (hb : (interior B).Nonempty) : False := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have he : a = b := Subsingleton.elim a b
  exact Set.disjoint_left.mp hd (interior_subset ha) (he ▸ interior_subset hb)
-- A map from an empty partition cannot be onto a continuum.
example {Y : Type v} [TopologicalSpace Y] (hY : IsContinuum Y)
    (f : (∅ : Set X) → Y) (hs : Function.Surjective f) : False := by
  obtain ⟨y⟩ := hY.1
  obtain ⟨x, _⟩ := hs y
  exact x.property
#print axioms Composants.mem_composant_self
#print axioms Composants.dense_composant
#print axioms Composants.isConnected_composant
#print axioms Composants.composants_eq_or_disjoint
#print axioms Composants.iUnion_composant
#print axioms Composants.composant_countable_union
#print axioms Composants.isMeagre_composant
#print axioms Composants.uncountably_many_composants
#print axioms Composants.alexandroff_continua
#print axioms Composants.IsSubcontinuum
#print axioms Composants.IsIndecomposable
#print axioms Composants.composant
#print axioms Composants.IsOpenCover
#print axioms Composants.IsPartitionBetween
#print axioms Composants.IsOmegaMap
#print axioms Composants.IsContinuum
