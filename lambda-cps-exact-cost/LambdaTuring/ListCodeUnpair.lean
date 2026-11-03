/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeSqrt
public meta import LambdaTuring.ListCodeSqrt

@[expose] public section

namespace LambdaTuring

def listCodeSqrtSquareInput : Turing.ToPartrec.Code :=
  listCodeBinary listCodeMul listCodeSqrt listCodeSqrt
def listCodeUnpairOffset : Turing.ToPartrec.Code :=
  listCodeBinary listCodeSub listCodeSqrtSquareInput .head
def listCodeUnpairCompare : Turing.ToPartrec.Code :=
  listCodeBinary listCodeSub listCodeUnpairOffset listCodeSqrt
def listCodeUnpairRemainder : Turing.ToPartrec.Code :=
  listCodeBinary listCodeSub listCodeSqrt listCodeUnpairOffset
def listCodeUnpairLeft : Turing.ToPartrec.Code :=
  listCodeIfPos listCodeUnpairCompare listCodeUnpairOffset listCodeSqrt
def listCodeUnpairRight : Turing.ToPartrec.Code :=
  listCodeIfPos listCodeUnpairCompare listCodeSqrt listCodeUnpairRemainder

theorem listCodeSqrtSquareInput_eval (n : Nat) :
    listCodeSqrtSquareInput.eval [n] = Part.some [n.sqrt*n.sqrt] := by
  apply listCodeBinary_eval listCodeMul listCodeSqrt listCodeSqrt [n] n.sqrt n.sqrt
  · simpa using listCodeSqrt_eval n []
  · simpa using listCodeSqrt_eval n []
  · simpa using listCodeMul_eval_general n.sqrt [n.sqrt]

theorem listCodeUnpairOffset_eval (n : Nat) :
    listCodeUnpairOffset.eval [n] = Part.some [n-n.sqrt*n.sqrt] := by
  apply listCodeBinary_eval listCodeSub listCodeSqrtSquareInput .head [n] (n.sqrt*n.sqrt) n
  · exact listCodeSqrtSquareInput_eval n
  · simp [Turing.ToPartrec.Code.head_eval]
  · simpa using listCodeSub_eval_general (n.sqrt*n.sqrt) [n]

theorem listCodeUnpairCompare_eval (n : Nat) :
    listCodeUnpairCompare.eval [n] = Part.some [n.sqrt-(n-n.sqrt*n.sqrt)] := by
  apply listCodeBinary_eval listCodeSub listCodeUnpairOffset listCodeSqrt [n]
    (n-n.sqrt*n.sqrt) n.sqrt
  · exact listCodeUnpairOffset_eval n
  · simpa using listCodeSqrt_eval n []
  · simpa using listCodeSub_eval_general (n-n.sqrt*n.sqrt) [n.sqrt]

theorem listCodeUnpairRemainder_eval (n : Nat) :
    listCodeUnpairRemainder.eval [n] = Part.some [n-n.sqrt*n.sqrt-n.sqrt] := by
  apply listCodeBinary_eval listCodeSub listCodeSqrt listCodeUnpairOffset [n]
    n.sqrt (n-n.sqrt*n.sqrt)
  · simpa using listCodeSqrt_eval n []
  · exact listCodeUnpairOffset_eval n
  · simpa using listCodeSub_eval_general n.sqrt [n-n.sqrt*n.sqrt]

theorem listCodeUnpairLeft_eval (n : Nat) :
    listCodeUnpairLeft.eval [n] = Part.some [n.unpair.1] := by
  have h := listCodeIfPos_eval listCodeUnpairCompare listCodeUnpairOffset listCodeSqrt [n]
    (n.sqrt-(n-n.sqrt*n.sqrt)) (n-n.sqrt*n.sqrt) n.sqrt
    (listCodeUnpairCompare_eval n) (listCodeUnpairOffset_eval n) (by simpa using listCodeSqrt_eval n [])
  by_cases hn : n-n.sqrt*n.sqrt < n.sqrt
  · have hp : n.sqrt-(n-n.sqrt*n.sqrt) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hn)
    simpa [listCodeUnpairLeft, Nat.unpair, hn, hp] using h
  · have hz : n.sqrt-(n-n.sqrt*n.sqrt) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
    simpa [listCodeUnpairLeft, Nat.unpair, hn, hz] using h

theorem listCodeUnpairRight_eval (n : Nat) :
    listCodeUnpairRight.eval [n] = Part.some [n.unpair.2] := by
  have h := listCodeIfPos_eval listCodeUnpairCompare listCodeSqrt listCodeUnpairRemainder [n]
    (n.sqrt-(n-n.sqrt*n.sqrt)) n.sqrt (n-n.sqrt*n.sqrt-n.sqrt)
    (listCodeUnpairCompare_eval n) (by simpa using listCodeSqrt_eval n []) (listCodeUnpairRemainder_eval n)
  by_cases hn : n-n.sqrt*n.sqrt < n.sqrt
  · have hp : n.sqrt-(n-n.sqrt*n.sqrt) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hn)
    simpa [listCodeUnpairRight, Nat.unpair, hn, hp] using h
  · have hz : n.sqrt-(n-n.sqrt*n.sqrt) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
    simpa [listCodeUnpairRight, Nat.unpair, hn, hz] using h

#print axioms listCodeUnpairLeft_eval
#print axioms listCodeUnpairRight_eval
end LambdaTuring
