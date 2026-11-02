/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryPreprocessor
public meta import LambdaTuring.UnaryPreprocessor
public import LambdaTuring.ThreeSymbolCodec
public meta import LambdaTuring.ThreeSymbolCodec

@[expose] public section

namespace LambdaTuring

open Turing.PartrecToTM2

def onesPositive : Nat → PosNum
  | 0 => .one
  | n + 1 => .bit1 (onesPositive n)

def onesNumber (n : Nat) : Nat := (onesPositive n : Nat)

theorem trPosNum_ones (n : Nat) :
    trPosNum (onesPositive n) = List.replicate (n + 1) Γ'.bit1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [onesPositive, trPosNum, ih, List.replicate_succ]

theorem trList_ones (n : Nat) :
    trList [onesNumber n] = List.replicate (n + 1) Γ'.bit1 ++ [.cons] := by
  simp [trList, trNat, onesNumber, trNum, trPosNum_ones]

def unaryPrefixSymbol : SimAlphabet :=
  (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

def unaryBitSymbol : SimAlphabet :=
  (false, Function.update (fun _ => none) K'.main (some Γ'.bit1))

set_option backward.isDefEq.respectTransparency false in
theorem tm0Input_ones (n : Nat) :
    tm0ListInput [onesNumber n] = unaryPrefixSymbol :: List.replicate (n + 1) unaryBitSymbol := by
  unfold tm0ListInput
  rw [trList_ones]
  simp [Turing.TM2to1.trInit, unaryPrefixSymbol, unaryBitSymbol,
    List.reverse_append]

theorem encodedInput_ones (n : Nat) :
    encodeSimSymbols (tm0ListInput [onesNumber n]) =
      encodeSimSymbol unaryPrefixSymbol ++
        (List.replicate (n + 1) (encodeSimSymbol unaryBitSymbol)).flatten := by
  rw [tm0Input_ones]
  simp [encodeSimSymbols, List.flatMap_replicate]

def prefixTail : List Machine.Symbol := .one :: .mark :: List.replicate 10 .one
def bitTail : List Machine.Symbol := .mark :: List.replicate 11 .one

theorem prefixBlock_eq : Machine.Symbol.mark :: prefixTail = encodeSimSymbol unaryPrefixSymbol := by decide
theorem bitBlock_eq : Machine.Symbol.one :: bitTail = encodeSimSymbol unaryBitSymbol := by decide

def simulatorInputPreprocessor :=
  Machine.unaryPreprocessor .mark .one prefixTail bitTail

theorem preprocessorWord_eq (n : Nat) :
    Machine.preprocessorWord .mark .one prefixTail bitTail n =
      encodeSimSymbols (tm0ListInput [onesNumber n]) := by
  rw [encodedInput_ones]
  simp only [Machine.preprocessorWord, prefixBlock_eq, bitBlock_eq]

theorem simulatorInputPreprocessor_runs (n : Nat) :
    let word := encodeSimSymbols (tm0ListInput [onesNumber n])
    let finish := Machine.sequenceRightConfig
      (n := Machine.prefixLoopSize .mark .one prefixTail bitTail)
      (⟨⟨2, by decide⟩, Machine.moveRight ⟨[], .blank, word ++ [.blank]⟩⟩ : Machine.Config 2)
    Machine.Reaches simulatorInputPreprocessor
      (Machine.preprocessorStart .mark .one prefixTail bitTail n) finish ∧
      Machine.Halted simulatorInputPreprocessor finish := by
  have hxs : prefixTail.length = 12 := by decide
  have hys : bitTail.length = 12 := by decide
  have ha : ∀ x ∈ Machine.Symbol.mark :: prefixTail, x ≠ .blank := by
    simp [prefixTail]
  have hb : ∀ x ∈ Machine.Symbol.one :: bitTail, x ≠ .blank := by
    simp [bitTail]
  have h := Machine.unaryPreprocessor_runs .mark .one prefixTail bitTail hxs hys ha hb n
  simpa [simulatorInputPreprocessor, preprocessorWord_eq] using h

theorem preprocessorTape_math (word : List Machine.Symbol) :
    Machine.mathTape (Machine.moveRight ⟨[], .blank, word ++ [.blank]⟩) =
      Turing.Tape.mk₁ word := by
  have hb (xs : List Machine.Symbol) :
      Turing.ListBlank.mk (xs ++ [.blank]) = Turing.ListBlank.mk xs := by
    apply Quotient.sound'
    right
    refine ⟨1, ?_⟩
    change xs ++ [.blank] = xs ++ List.replicate 1 Machine.Symbol.blank
    rfl
  have he : Turing.ListBlank.mk [Machine.Symbol.blank] = Turing.ListBlank.mk [] := by
    simpa using hb []
  cases word with
  | nil =>
    simp [Machine.mathTape, Machine.moveRight, Turing.Tape.mk₁, Turing.Tape.mk₂,
      Turing.Tape.mk', he]
    rfl
  | cons a xs => simp [Machine.mathTape, Machine.moveRight, Turing.Tape.mk₁, Turing.Tape.mk₂,
      Turing.Tape.mk', he, hb]

theorem simulatorInputPreprocessor_correct (n : Nat) :
    ∃ c, Machine.Reaches simulatorInputPreprocessor (Machine.initial n) c ∧
      Machine.Halted simulatorInputPreprocessor c ∧
      Machine.mathTape c.tape = Turing.Tape.mk₁ (encodeSimSymbols (tm0ListInput [onesNumber n])) := by
  let word := encodeSimSymbols (tm0ListInput [onesNumber n])
  let finish := Machine.sequenceRightConfig
    (n := Machine.prefixLoopSize .mark .one prefixTail bitTail)
    (⟨⟨2, by decide⟩, Machine.moveRight ⟨[], .blank, word ++ [.blank]⟩⟩ : Machine.Config 2)
  refine ⟨finish, ?_, ?_, ?_⟩
  · simpa [simulatorInputPreprocessor, Machine.preprocessorStart, Machine.initial, finish, word] using
      (simulatorInputPreprocessor_runs n).1
  · simpa [finish, word] using (simulatorInputPreprocessor_runs n).2
  · exact preprocessorTape_math word

theorem onesNumber_succ (n : Nat) : onesNumber (n + 1) = 2 * onesNumber n + 1 := by
  simp [onesNumber, onesPositive, PosNum.cast_bit1, two_mul]

theorem onesNumber_add_one (n : Nat) : onesNumber n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [onesNumber_succ, pow_succ]
    omega

#eval encodeSimSymbol unaryPrefixSymbol
#eval encodeSimSymbol unaryBitSymbol
#print axioms encodedInput_ones
#print axioms simulatorInputPreprocessor_runs
#print axioms preprocessorTape_math
#print axioms simulatorInputPreprocessor_correct
#print axioms onesNumber_add_one
end LambdaTuring
