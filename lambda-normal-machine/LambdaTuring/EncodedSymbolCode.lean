/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedListCode
public meta import LambdaTuring.EncodedListCode
public import LambdaTuring.MachineCoding
public meta import LambdaTuring.MachineCoding

@[expose] public section

namespace LambdaTuring.Machine

#eval Encodable.encode Symbol.blank
#eval Encodable.encode Symbol.one
#eval Encodable.encode Symbol.mark
#eval Encodable.encode Action.left
#eval Encodable.encode Action.right
#eval Encodable.encode (Action.write Symbol.blank)
#eval Encodable.encode (Action.write Symbol.one)
#eval Encodable.encode (Action.write Symbol.mark)

theorem symbol_encoded (s : Symbol) : Encodable.encode s = symbolIndex s := by
  cases s <;> rfl

theorem tape_encoded (t : Tape) : Encodable.encode t =
    Nat.pair (Encodable.encode t.left)
      (Nat.pair (Encodable.encode t.head) (Encodable.encode t.right)) := by
  rfl

def tapeLeftCode : Nat.Partrec.Code := .left
def tapeHeadCode : Nat.Partrec.Code := .comp .left .right
def tapeRightCode : Nat.Partrec.Code := .comp .right .right

theorem tapeLeftCode_eval (t : Tape) :
    tapeLeftCode.eval (Encodable.encode t) = Part.some (Encodable.encode t.left) := by
  rw [tape_encoded]
  simp [tapeLeftCode, Nat.Partrec.Code.eval]

theorem tapeHeadCode_eval (t : Tape) :
    tapeHeadCode.eval (Encodable.encode t) = Part.some (Encodable.encode t.head) := by
  change (Nat.Partrec.Code.eval .right (Encodable.encode t)).bind
    (fun x => Nat.Partrec.Code.eval .left x) = _
  rw [tape_encoded]
  simp [Nat.Partrec.Code.eval, Part.bind_some]

theorem tapeRightCode_eval (t : Tape) :
    tapeRightCode.eval (Encodable.encode t) = Part.some (Encodable.encode t.right) := by
  change (Nat.Partrec.Code.eval .right (Encodable.encode t)).bind
    (fun x => Nat.Partrec.Code.eval .right x) = _
  rw [tape_encoded]
  simp [Nat.Partrec.Code.eval, Part.bind_some]

#print axioms tapeLeftCode
#print axioms tapeHeadCode
#print axioms tapeRightCode
#print axioms tapeHeadCode_eval

end LambdaTuring.Machine
