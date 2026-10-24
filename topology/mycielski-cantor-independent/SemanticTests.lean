module
public import MycielskiSolution
public section
open Set TopologicalSpace
open scoped Topology
#check Mycielski.exists_cantor_independent
example {X : Type*} [TopologicalSpace X] [PolishSpace X] [PerfectSpace X]
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (R : ℕ → Set (X × X))
    (ho : ∀ n, IsOpen (R n)) (hd : ∀ n, Dense (R n)) :
    ∃ e : (ℕ → Bool) → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
      ∀ s t, s ≠ t → ∀ n, (e s, e t) ∈ R n :=
  Mycielski.exists_cantor_independent hU hne R ho hd

-- BEGIN material-imported-definition audit
example : Mycielski.CantorSpace = (ℕ → Bool) := rfl
example (n : ℕ) : Continuous (fun x : Mycielski.CantorSpace => x n) := continuous_apply n
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    Dense s ↔ ∀ x, x ∈ closure s := Iff.rfl
example {X : Type*} (e : Mycielski.CantorSpace → X) (x : X) :
    x ∈ range e ↔ ∃ s, e s = x := Iff.rfl
example {X : Type*} [TopologicalSpace X] [PerfectSpace X] (x : X)
    (V : Set X) (hV : V ∈ 𝓝 x) : ∃ y ∈ V, y ≠ x := by
  obtain ⟨y, hy, hne⟩ := (preperfect_iff_nhds.mp (PerfectSpace.univ_preperfect (α := X)))
    x (mem_univ x) V hV
  exact ⟨y, hy.1, hne⟩
example {X : Type*} [TopologicalSpace X] [PolishSpace X] : SecondCountableTopology X := inferInstance
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
      @CompleteSpace X m.toUniformSpace := IsCompletelyMetrizableSpace.complete
example {X : Type*} [TopologicalSpace X] (e : Mycielski.CantorSpace → X)
    (he : Topology.IsClosedEmbedding e) : Continuous e := he.continuous
example {X : Type*} [TopologicalSpace X] (e : Mycielski.CantorSpace → X)
    (he : Topology.IsClosedEmbedding e) : Function.Injective e := he.injective
example {X : Type*} [TopologicalSpace X] (e : Mycielski.CantorSpace → X)
    (he : Topology.IsClosedEmbedding e) : IsClosed (range e) := he.isClosed_range
example {X : Type*} [TopologicalSpace X] (e : Mycielski.CantorSpace → X)
    (he : Topology.IsClosedEmbedding e) :
    (inferInstance : TopologicalSpace Mycielski.CantorSpace) =
      TopologicalSpace.induced e inferInstance := he.isInducing.eq_induced
example {X : Type*} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ×ˢ V) := hU.prod hV
example {X : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (X × X)) =
      TopologicalSpace.induced Prod.fst t ⊓ TopologicalSpace.induced Prod.snd t := rfl
-- END material-imported-definition audit
