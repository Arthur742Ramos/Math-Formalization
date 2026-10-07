module
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Connected.PathConnected
@[expose] public section
open Set Topology TopologicalSpace

example {Y : Type*} [TopologicalSpace Y] (x y : Y) : Joined x y ↔ Nonempty (Path x y) := Iff.rfl
example {Y : Type*} [TopologicalSpace Y] (x : Y) : pathComponent x = {y | Nonempty (Path x y)} := rfl
example {X : Type*} [TopologicalSpace X] : (inferInstance : TopologicalSpace (NonemptyCompacts X)) = TopologicalSpace.induced ((↑) : NonemptyCompacts X → Set X) (TopologicalSpace.vietoris X) := rfl
example {X : Type*} [TopologicalSpace X] (K : Set X) : IsConnected K ↔ K.Nonempty ∧ IsPreconnected K := Iff.rfl
