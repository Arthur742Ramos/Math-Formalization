/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.BlockFiniteTM0
public meta import LambdaTuring.BlockFiniteTM0

@[expose] public section

namespace LambdaTuring

/-- A small complete execution check for the generic extraction. This does
    not materialize the much larger compiled block-machine table. -/
def tinyTM1 : Unit → Turing.TM1.Stmt Machine.Symbol Unit Unit := fun _ => .halt

abbrev tinyStateCount := (tm1RawTail tinyTM1 [()] [()]).length

def tinyProgram : Machine.Program tinyStateCount := by
  letI : Inhabited (Fin (tinyStateCount + 1)) := ⟨0⟩
  exact Machine.tableOfMathlib (tm1NumberedMachine tinyTM1 [()] [()])

def tinyFinal : Machine.Config tinyStateCount :=
  ⟨⟨1, by decide⟩, (Machine.initial (states := tinyStateCount) 0).tape⟩

theorem tinyProgram_step : Machine.step tinyProgram (Machine.initial 0) = some tinyFinal := by decide

theorem tinyProgram_halted : Machine.Halted tinyProgram tinyFinal := by
  change Machine.step tinyProgram tinyFinal = none
  decide

theorem tinyProgram_yields_zero : Machine.Yields tinyProgram 0 0 := by
  refine ⟨tinyFinal, .step tinyProgram_step (.refl _), tinyProgram_halted, ?_⟩
  decide

#eval tinyProgram.table
#eval (Machine.step tinyProgram (Machine.initial 0)).map fun c => (c.state.val, c.tape.head, c.tape.right)
#eval ((Machine.step tinyProgram (Machine.initial 0)).bind (Machine.step tinyProgram)).isNone

#print axioms tinyProgram_yields_zero
end LambdaTuring
