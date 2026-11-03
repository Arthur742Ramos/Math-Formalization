/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.ConcreteNormalMachineComplete
public meta import LambdaTuring.ConcreteNormalMachineComplete
@[expose] public section

namespace LambdaTuring

/-- A single explicit finite machine distinguishes numerical normal forms,
nonnumerical normal forms, and the absence of a reachable normal form. -/
theorem normalMachine_exists :
    ∃ (states : Nat) (p : Machine.Program states), ∀ t : Term,
      (∀ n, Machine.Yields p (directTermNumber t) (n + 1) ↔ Reaches t (church n)) ∧
      (Machine.Yields p (directTermNumber t) 0 ↔
        (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧ ¬ ∃ n, Reaches t (church n)) ∧
      ((¬ ∃ d, Machine.Reaches p (Machine.initial (directTermNumber t)) d ∧ Machine.Halted p d) ↔
        ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧
      (∀ d, Machine.Reaches p (Machine.initial (directTermNumber t)) d → Machine.Halted p d →
        ∃ m, Machine.decode (d.tape.head :: d.tape.right) = some m) := by
  refine ⟨_, normalObserverMachine, ?_⟩
  intro t
  exact ⟨normalObserverMachine_numeral t, normalObserverMachine_nonnumeral t,
    normalObserverMachine_no_halt t, normalObserverMachine_halt_decodable t⟩

#print axioms normalMachine_exists
end LambdaTuring
