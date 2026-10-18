module

import CollectionwiseSolution

open Set Filter Function Topology

universe u v
variable {ι : Type u} {X : Type v} [TopologicalSpace X]

-- Empty members at arbitrarily many indices impose no nonemptiness assumption.
example : Collectionwise.IsDiscreteFamily (fun _ : ι => (∅ : Set X)) := by
  intro x
  refine ⟨univ, Filter.univ_mem, ?_⟩
  simp

-- Empty ambient and empty index types are accepted by the actual definitions.
example [IsEmpty X] (F : ι → Set X) : Collectionwise.IsDiscreteFamily F :=
  fun x => isEmptyElim x

example [IsEmpty ι] (F : ι → Set X) : Collectionwise.IsDiscreteFamily F := by
  intro x
  exact ⟨univ, Filter.univ_mem, fun i => isEmptyElim i⟩

-- Local finiteness alone permits two equal nonempty members; discreteness does not.
example (x : X) : ¬ Collectionwise.IsDiscreteFamily (fun _ : Bool => ({x} : Set X)) := by
  intro h
  have hd := h.pairwiseDisjoint (i := false) (j := true) (by decide)
  exact hd.le_bot ⟨rfl, rfl⟩

-- The arbitrary-family expansion theorem does not silently require T1 or normality.
example [ParacompactSpace X] (F : Bool → Set X) : Collectionwise.HasOpenExpansion F :=
  Collectionwise.exists_open_expansion (locallyFinite_of_finite F)

-- An actual finite indiscrete model permits overlap and uses no T1 instance.
example (F : Bool → Set Bool) :
    letI : TopologicalSpace Bool := ⊤
    Collectionwise.HasOpenExpansion F := by
  let : TopologicalSpace Bool := ⊤
  exact Collectionwise.exists_open_expansion (locallyFinite_of_finite F)

example : letI : TopologicalSpace Bool := ⊤; ¬ T1Space Bool := by
  let : TopologicalSpace Bool := ⊤
  intro h
  let _ := h
  have ho : IsOpen ({false}ᶜ : Set Bool) := isClosed_singleton.isOpen_compl
  rcases (TopologicalSpace.isOpen_top_iff _).mp ho with he | he
  · have hh := congrArg (fun s : Set Bool => true ∈ s) he
    simp at hh
  · have hh := congrArg (fun s : Set Bool => false ∈ s) he
    simp at hh

-- Invoke the selected separation theorem with an empty index, not just its definition.
example [ParacompactSpace X] [T2Space X] [IsEmpty ι] (F : ι → Set X) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, F i ⊆ U i) ∧
      Collectionwise.IsDiscreteFamily U ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
  apply Collectionwise.paracompact_hausdorff_collectionwise
  · intro x
    exact ⟨univ, Filter.univ_mem, fun i => isEmptyElim i⟩
  · exact fun i => isEmptyElim i

-- The same selected theorem accepts an empty ambient space and arbitrary indices.
example [ParacompactSpace X] [T2Space X] [IsEmpty X] (F : ι → Set X) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, F i ⊆ U i) ∧
      Collectionwise.IsDiscreteFamily U ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) := by
  apply Collectionwise.paracompact_hausdorff_collectionwise
  · exact fun x => isEmptyElim x
  · intro i
    have : F i = ∅ := by ext x; exact isEmptyElim x
    rw [this]
    exact isClosed_empty

-- Independently elaborate the same five theorem and two literal-definition contracts.

example [ParacompactSpace X] (F : ι → Set X) (hF : LocallyFinite F) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧ ∀ i, F i ⊆ U i :=
  Collectionwise.exists_open_expansion hF

example [ParacompactSpace X] [NormalSpace X] (F O : ι → Set X)
    (hF : Collectionwise.IsDiscreteFamily F) (hc : ∀ i, IsClosed (F i))
    (ho : ∀ i, IsOpen (O i)) (hsub : ∀ i, F i ⊆ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧
      (∀ i, F i ⊆ U i) ∧ (∀ i, closure (U i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) ∧
      Collectionwise.IsDiscreteFamily U :=
  Collectionwise.exists_discrete_expansion hF hc ho hsub

example (F : ι → Set X) : Collectionwise.IsDiscreteFamily F ↔
    ∀ x : X, ∃ N ∈ 𝓝 x, ∀ i ∈ {i | (F i ∩ N).Nonempty},
      ∀ j ∈ {i | (F i ∩ N).Nonempty}, i = j := Iff.rfl

example [ParacompactSpace X] [NormalSpace X] (F O : ι → Set X)
    (hf : LocallyFinite F) (hc : ∀ i, IsClosed (F i))
    (ho : ∀ i, IsOpen (O i)) (hsub : ∀ i, F i ⊆ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧
      (∀ i, F i ⊆ U i) ∧ ∀ i, closure (U i) ⊆ O i :=
  Collectionwise.exists_subordinate_expansion hf hc ho hsub

example (F : ι → Set X) (hc : ∀ i, IsClosed (F i)) :
    Collectionwise.IsDiscreteFamily F ↔ LocallyFinite F ∧ Pairwise (Disjoint on F) :=
  Collectionwise.discrete_closed_iff hc

example [ParacompactSpace X] [T2Space X] (F : ι → Set X)
    (hf : Collectionwise.IsDiscreteFamily F) (hc : ∀ i, IsClosed (F i)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, F i ⊆ U i) ∧
      Collectionwise.IsDiscreteFamily U ∧
      Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))) :=
  Collectionwise.paracompact_hausdorff_collectionwise hf hc

example (F : ι → Set X) : Collectionwise.HasOpenExpansion F ↔
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ LocallyFinite U ∧ ∀ i, F i ⊆ U i := Iff.rfl
