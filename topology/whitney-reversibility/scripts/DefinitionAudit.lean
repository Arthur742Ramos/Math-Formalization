/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.Clopen

@[expose] public section
open Set Topology TopologicalSpace
example {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsConnected K ↔ K.Nonempty ∧ IsPreconnected K := Iff.rfl
example {X : Type*} [TopologicalSpace X] (K : NonemptyCompacts X) :
    K.toCompacts.carrier = (K : Set X) := rfl
