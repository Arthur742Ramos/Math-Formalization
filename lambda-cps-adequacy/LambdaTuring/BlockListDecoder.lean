/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ThreeSymbolCodec
public meta import LambdaTuring.ThreeSymbolCodec

@[expose] public section

namespace LambdaTuring

/-- Decode a finite sequence of complete blocks; incomplete or malformed blocks fail. -/
def decodeBlocks : Nat → List Machine.Symbol → Option (List SimAlphabet)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, xs@(_ :: _) => do
      let a ← decodeSymbolBlock (xs.take 13)
      let rest ← decodeBlocks fuel (xs.drop 13)
      some (decodeSimAlphabet a :: rest)

def decodeBlockList (xs : List Machine.Symbol) : Option (List SimAlphabet) :=
  decodeBlocks xs.length xs

theorem decodeBlocks_encoded (xs : List SimAlphabet) (fuel : Nat)
    (h : xs.length ≤ fuel) : decodeBlocks fuel (encodeSimSymbols xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons a xs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have h' : xs.length ≤ fuel := by simpa using h
      have hl : (encodeSimSymbol a).length = 13 := encodeSymbolBlock_length _
      have he : encodeSimSymbol a ≠ [] := by intro he; simp [he] at hl
      cases ha : encodeSimSymbol a with
      | nil => exact (he ha).elim
      | cons b bs =>
        change decodeBlocks (fuel + 1) (encodeSimSymbol a ++ encodeSimSymbols xs) = _
        rw [ha]
        simp only [List.cons_append, decodeBlocks]
        have htake : (b :: bs ++ encodeSimSymbols xs).take 13 = encodeSimSymbol a := by
          rw [← ha, ← hl]
          simp
        have hdrop : (b :: bs ++ encodeSimSymbols xs).drop 13 = encodeSimSymbols xs := by
          rw [← ha, ← hl]
          simp
        simp only [List.cons_append] at htake hdrop
        rw [htake, hdrop]
        simp [encodeSimSymbol, decodeSymbolBlock_encode, decode_encodeSimAlphabet, ih fuel h']

theorem encodeSimSymbols_length (xs : List SimAlphabet) :
    (encodeSimSymbols xs).length = xs.length * 13 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (encodeSimSymbol a ++ encodeSimSymbols xs).length = (xs.length + 1) * 13
    simp [List.length_append, encodeSimSymbol, encodeSymbolBlock_length, ih, Nat.add_mul, Nat.add_comm]

theorem decodeBlockList_encoded (xs : List SimAlphabet) :
    decodeBlockList (encodeSimSymbols xs) = some xs := by
  apply decodeBlocks_encoded
  rw [encodeSimSymbols_length]
  omega

example : decodeBlockList [.one] = none := rfl

#print axioms decodeBlocks_encoded
#print axioms decodeBlockList_encoded
end LambdaTuring
