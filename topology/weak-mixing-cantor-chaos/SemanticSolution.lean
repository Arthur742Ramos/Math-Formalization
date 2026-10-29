module
public import ChaosSolution

open Set Function Filter TopologicalSpace CantorChaos
open scoped Topology

-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    OpenTransitive f ↔ ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ n : ℕ, ∃ z ∈ U, f^[n] z ∈ V := Iff.rfl

example {X : Type*} (f : X → X) (x y : X) :
    pairMap f (x, y) = (f x, f y) := rfl

example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    DenseOrbit f x ↔ Dense (range (fun n : ℕ => f^[n] x)) := Iff.rfl

example {X : Type*} (f : X → X) (x : X) : f^[0] x = x := rfl
example {X : Type*} (f : X → X) (n : ℕ) (x : X) : f^[n+1] x = f^[n] (f x) := rfl
example {X : Type*} (s : Set X) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Dense C ↔ ∀ x, x ∈ closure C := Iff.rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    SecondCountableTopology X := inferInstance
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    IsCompletelyMetrizableSpace X := inferInstance
example {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X] :
    ∀ x : X, NeBot (𝓝[≠] x) := PerfectSpace.not_isolated
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y)
    (he : Topology.IsClosedEmbedding e) : Continuous e ∧ Injective e := ⟨he.continuous, he.injective⟩
-- END material-imported-definition audit

/-- The selected conclusion supplies positive-time close and separated returns
for each fixed distinct pair; the embedding and common scale are outputs. -/
example {X : Type*} [MetricSpace X] [PolishSpace X] [PerfectSpace X] [Nontrivial X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f))
    (U : Set X) (hU : IsOpen U) (hneU : U.Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ e : Mycielski.CantorSpace → X,
      Continuous e ∧ Injective e ∧ range e ⊆ U ∧
      ∀ s t, s ≠ t → ∀ ε : ℝ, 0 < ε →
        (∃ n : ℕ, 0 < n ∧ dist (f^[n] (e s)) (f^[n] (e t)) < ε) ∧
        (∃ n : ℕ, 0 < n ∧ δ < dist (f^[n] (e s)) (f^[n] (e t))) := by
  obtain ⟨δ, hδ, hall⟩ := cantor_uniform_scrambled f hf ht
  obtain ⟨e, he, heU, hpair⟩ := hall U hU hneU
  refine ⟨δ, hδ, e, he.continuous, he.injective, heU, ?_⟩
  intro s t hst ε hε
  obtain ⟨hclose, hfar⟩ := hpair s t hst
  obtain ⟨n, hn, hc⟩ := hclose ε hε 1
  obtain ⟨m, hm, hs⟩ := hfar 1
  exact ⟨⟨n, by omega, hc⟩, ⟨m, by omega, hs⟩⟩

-- Further statement-driven bridges: product topology, distance and closed image.
example : Mycielski.CantorSpace = (ℕ → Bool) := rfl
example (i : ℕ) : Continuous (fun x : Mycielski.CantorSpace => x i) := continuous_apply i
example : IsOpen ({true} : Set Bool) := isOpen_discrete _
example {X Y : Type*} (f : X → Y) (y : Y) :
    y ∈ range f ↔ ∃ x, f x = y := Iff.rfl
example {X : Type*} [Nontrivial X] : ∃ x y : X, x ≠ y := exists_pair_ne X
example {X : Type*} [MetricSpace X] (x y : X) (h : x ≠ y) :
    0 < dist x y := dist_pos.mpr h
example {X : Type*} [MetricSpace X] (ε : ℝ) :
    IsOpen {p : X × X | dist p.1 p.2 < ε} :=
  isOpen_lt (continuous_fst.dist continuous_snd) continuous_const
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y)
    (he : Topology.IsClosedEmbedding e) : IsClosed (range e) := he.isClosed_range

/-- This checks the global δ before the universal open-set quantifier, and
retains the closed embedding and arbitrarily late close and far returns. -/
example {X : Type*} [MetricSpace X] [PolishSpace X] [PerfectSpace X] [Nontrivial X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ e : Mycielski.CantorSpace → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
        ∀ s t, s ≠ t →
          (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, dist (f^[n] (e s)) (f^[n] (e t)) < ε) ∧
          (∀ N : ℕ, ∃ n ≥ N, δ < dist (f^[n] (e s)) (f^[n] (e t))) :=
  cantor_uniform_scrambled f hf ht

example {X : Type*} [TopologicalSpace X] [PolishSpace X] [PerfectSpace X]
    (f : X → X) (hf : Continuous f) (ht : OpenTransitive (pairMap f))
    (U : Set X) (hU : IsOpen U) (hneU : U.Nonempty) :
    ∃ e : Mycielski.CantorSpace → X, Topology.IsClosedEmbedding e ∧ range e ⊆ U ∧
      ∀ s t, s ≠ t → DenseOrbit (pairMap f) (e s, e t) :=
  cantor_dense_pair_orbits f hf ht hU hneU
