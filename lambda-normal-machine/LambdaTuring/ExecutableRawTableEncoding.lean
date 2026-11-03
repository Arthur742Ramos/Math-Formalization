/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UniformMachineSyntax
public meta import LambdaTuring.UniformMachineSyntax
public import LambdaTuring.EncodedSymbolCode
public meta import LambdaTuring.EncodedSymbolCode

@[expose] public section

namespace LambdaTuring.Machine

/-- Direct data-only encoding of the finite raw instruction table. -/
def rawActionNumber : Action → Nat
  | .left => 0
  | .right => 1
  | .write .blank => 2
  | .write .one => 3
  | .write .mark => 4

def rawEntryNumber : Option (Nat × Action) → Nat
  | none => 0
  | some (q, a) => Nat.succ (Nat.pair q (rawActionNumber a))

def rawTableNumber : RawTable → Nat
  | [] => 0
  | e :: es => Nat.succ (Nat.pair (rawEntryNumber e) (rawTableNumber es))

theorem rawActionNumber_eq (a : Action) : rawActionNumber a = Encodable.encode a := by
  cases a with
  | left | right => rfl
  | write s => cases s <;> rfl

theorem rawEntryNumber_eq (e : Option (Nat × Action)) : rawEntryNumber e = Encodable.encode e := by
  cases e with
  | none => rfl
  | some p =>
    rcases p with ⟨q, a⟩
    simp [rawEntryNumber, rawActionNumber_eq, Encodable.encode_prod_val]

theorem rawTableNumber_eq (p : RawTable) : rawTableNumber p = Encodable.encode p := by
  induction p with
  | nil => rfl
  | cons e es ih => simp [rawTableNumber, rawEntryNumber_eq, ih, Encodable.encode_list_cons]

#print axioms rawActionNumber
#print axioms rawEntryNumber
#print axioms rawTableNumber
#print axioms rawTableNumber_eq
end LambdaTuring.Machine
