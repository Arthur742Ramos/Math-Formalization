/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.ParametricNormalMachine
public meta import LambdaTuring.ParametricNormalMachine
@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- Explicit code, kept irreducible during machine-theorem elaboration so the
finite table need not be expanded by definitional reduction. -/
@[irreducible] def finiteNormalObserverCode : Code := directNormalObserverCode

theorem finiteNormalObserverCode_eval (t : Term) :
    Code.eval finiteNormalObserverCode (directTermNumber t) =
      (normalObservation t).map Encodable.encode := by
  rw [finiteNormalObserverCode]
  exact directNormalObserverCode_eval t

/-- One fixed standard finite machine consumes the direct term encoding. -/
def normalObserverMachine := compiledUnaryMachine finiteNormalObserverCode

theorem normalObserverMachine_yields (t : Term) (r : Option Nat) :
    Machine.Yields normalObserverMachine (directTermNumber t) (Encodable.encode r) ↔
      r ∈ normalObservation t := by
  exact codeMachine_yields finiteNormalObserverCode finiteNormalObserverCode_eval t r

theorem normalObserverMachine_numeral (t : Term) (n : Nat) :
    Machine.Yields normalObserverMachine (directTermNumber t) (n + 1) ↔
      Reaches t (church n) := by
  exact codeMachine_numeral finiteNormalObserverCode finiteNormalObserverCode_eval t n

theorem normalObserverMachine_nonnumeral (t : Term) :
    Machine.Yields normalObserverMachine (directTermNumber t) 0 ↔
      (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧ ¬ ∃ n, Reaches t (church n) := by
  exact codeMachine_nonnumeral finiteNormalObserverCode finiteNormalObserverCode_eval t

theorem normalObserverMachine_no_halt (t : Term) :
    (¬ ∃ d, Machine.Reaches normalObserverMachine (Machine.initial (directTermNumber t)) d ∧
      Machine.Halted normalObserverMachine d) ↔
      ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v := by
  exact codeMachine_no_halt finiteNormalObserverCode finiteNormalObserverCode_eval t

#print axioms finiteNormalObserverCode_eval
#print axioms normalObserverMachine_numeral
#print axioms normalObserverMachine_nonnumeral
#print axioms normalObserverMachine_no_halt
end LambdaTuring
