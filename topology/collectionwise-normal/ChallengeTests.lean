module

import CollectionwiseChallenge

open Set Filter Function Topology

universe u v
variable {ι : Type u} {X : Type v} [TopologicalSpace X]

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
