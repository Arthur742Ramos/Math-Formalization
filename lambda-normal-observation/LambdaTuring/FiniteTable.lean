/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Machine
public meta import LambdaTuring.Machine

@[expose] public section

namespace LambdaTuring.Machine

def symbolOfIndex (i : Nat) : Symbol :=
  match i % 3 with
  | 0 => .blank
  | 1 => .one
  | _ => .mark

/-- Enumerate an arbitrary finite-state transition function as a finite table. -/
def tableOfFunction {states : Nat}
    (f : Fin (states + 1) → Symbol → Option (Fin (states + 1) × Action)) : Program states :=
  ⟨List.ofFn (fun (i : Fin ((states + 1) * 3)) =>
    f ⟨i.val / 3, by omega⟩ (symbolOfIndex i.val))⟩

theorem tableOfFunction_instruction {states : Nat}
    (f : Fin (states + 1) → Symbol → Option (Fin (states + 1) × Action))
    (q : Fin (states + 1)) (s : Symbol) :
    instruction (tableOfFunction f) q s = f q s := by
  have hq := q.isLt
  have hbound : q.val * 3 + symbolIndex s < (states + 1) * 3 := by
    cases s <;> simp [symbolIndex] <;> omega
  have hdiv : (q.val * 3 + symbolIndex s) / 3 = q.val := by
    cases s <;> simp [symbolIndex] <;> omega
  have hsym : symbolOfIndex (q.val * 3 + symbolIndex s) = s := by
    cases s <;> simp [symbolIndex, symbolOfIndex]
  simp only [instruction, tableOfFunction, List.getElem?_ofFn, dite_eq_left hbound, Option.getD_some]
  have hfin : (⟨(q.val * 3 + symbolIndex s) / 3, by omega⟩ : Fin (states + 1)) = q := Fin.ext hdiv
  rw [hfin, hsym]

#print axioms tableOfFunction_instruction

end LambdaTuring.Machine
