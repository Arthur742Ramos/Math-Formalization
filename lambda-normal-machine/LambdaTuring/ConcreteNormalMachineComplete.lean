/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.ConcreteNormalMachine
public meta import LambdaTuring.ConcreteNormalMachine
public import LambdaTuring.MachineHaltDecodable
public meta import LambdaTuring.MachineHaltDecodable
@[expose] public section

namespace LambdaTuring

/-- Every actual terminal configuration has a valid unary observation. -/
theorem normalObserverMachine_halt_decodable (t : Term)
    (d : Machine.Config _)
    (hr : Machine.Reaches normalObserverMachine (Machine.initial (directTermNumber t)) d)
    (hh : Machine.Halted normalObserverMachine d) :
    ∃ m, Machine.decode (d.tape.head :: d.tape.right) = some m := by
  exact compiledUnaryMachine_halt_decodable finiteNormalObserverCode (directTermNumber t) d hr hh

/-- With no normal form, every finite machine run can take another step;
conversely such continuing runs rule out a normal form. -/
theorem normalObserverMachine_continues_iff (t : Term) :
    (∀ d, Machine.Reaches normalObserverMachine (Machine.initial (directTermNumber t)) d →
      ∃ e, Machine.step normalObserverMachine d = some e) ↔
      ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v := by
  constructor
  · intro h
    apply (normalObserverMachine_no_halt t).1
    rintro ⟨d, hr, hh⟩
    obtain ⟨e, he⟩ := h d hr
    change Machine.step normalObserverMachine d = none at hh
    rw [hh] at he
    cases he
  · intro h d hr
    have hno := (normalObserverMachine_no_halt t).2 h
    cases hs : Machine.step normalObserverMachine d with
    | none => exact False.elim (hno ⟨d, hr, hs⟩)
    | some e => exact ⟨e, rfl⟩

#print axioms normalObserverMachine_halt_decodable
#print axioms normalObserverMachine_continues_iff
end LambdaTuring
