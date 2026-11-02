/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryPrefixBlocks
public meta import LambdaTuring.UnaryPrefixBlocks
public import LambdaTuring.ScanBack
public meta import LambdaTuring.ScanBack

@[expose] public section

namespace LambdaTuring.Machine

def unaryPreprocessor (a b : Symbol) (xs ys : List Symbol) :=
  sequenceProgram (prefixAndUnaryLoop a b xs ys) scanBack

abbrev insertSize (a : Symbol) (xs : List Symbol) := 78 + 2 * (a :: xs).length + 1
abbrev loopSize (b : Symbol) (ys : List Symbol) := blockBodySize b ys + blockFinalSize b ys + 5
abbrev prefixLoopSize (a b : Symbol) (xs ys : List Symbol) := insertSize a xs + loopSize b ys + 1

def preprocessorStart (a b : Symbol) (xs ys : List Symbol) (n : Nat) :
    Config (prefixLoopSize a b xs ys + 2 + 1) :=
  ⟨⟨0, by omega⟩, ⟨[], .one, List.replicate n .one⟩⟩

def preprocessorWord (a b : Symbol) (xs ys : List Symbol) (n : Nat) : List Symbol :=
  (a :: xs) ++ (List.replicate (n + 1) (b :: ys)).flatten

theorem preprocessorWord_nonblank (a b : Symbol) (xs ys : List Symbol) (n : Nat)
    (ha : ∀ x ∈ a :: xs, x ≠ .blank) (hb : ∀ x ∈ b :: ys, x ≠ .blank) :
    ∀ x ∈ preprocessorWord a b xs ys n, x ≠ .blank := by
  intro x hx
  simp only [preprocessorWord, List.mem_append, List.mem_flatten, List.mem_replicate] at hx
  rcases hx with h | ⟨block, ⟨_, rfl⟩, h⟩
  · exact ha x h
  · exact hb x h

theorem unaryPreprocessor_runs (a b : Symbol) (xs ys : List Symbol)
    (hxs : xs.length = 12) (hys : ys.length = 12)
    (ha : ∀ x ∈ a :: xs, x ≠ .blank) (hb : ∀ x ∈ b :: ys, x ≠ .blank) (n : Nat) :
    let word := preprocessorWord a b xs ys n
    let finish := sequenceRightConfig (n := prefixLoopSize a b xs ys)
      (⟨⟨2, by decide⟩, moveRight ⟨[], .blank, word ++ [.blank]⟩⟩ : Config 2)
    Reaches (unaryPreprocessor a b xs ys) (preprocessorStart a b xs ys n) finish ∧
      Halted (unaryPreprocessor a b xs ys) finish := by
  let word := preprocessorWord a b xs ys n
  have hall : ∀ x ∈ word, x ≠ .blank := preprocessorWord_nonblank a b xs ys n ha hb
  have hne : word.reverse ≠ [] := by simp [word, preprocessorWord]
  cases he : word.reverse with
  | nil => exact (hne he).elim
  | cons z zs =>
    have hz : z ≠ .blank := by
      apply hall z
      have hzrev : z ∈ word.reverse := by rw [he]; simp
      simpa using hzrev
    have hzs : ∀ x ∈ zs, x ≠ .blank := by
      intro x hx
      apply hall x
      have : x ∈ word.reverse := by rw [he]; simp [hx]
      simpa using this
    have hw : word = zs.reverse ++ [z] := by
      have h := congrArg List.reverse he
      simpa [List.reverse_cons] using h
    let pStart := sequenceLeftConfig (n := insertSize a xs) (m := loopSize b ys)
      (sequenceLeftConfig (n := 78) (m := 2 * (a :: xs).length)
        (sequenceLeftConfig (n := 65) (m := 12)
          (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart [] n))))
    let pEnd := sequenceRightConfig (n := insertSize a xs)
      (unaryBlockFinish b ys ((a :: xs).reverse ++ []) n)
    have hp := prefixAndUnaryLoop_runs a b xs ys hxs hys [] n
    have hstart : Reaches (prefixAndUnaryLoop a b xs ys) pStart pEnd := by
      simpa [pStart, pEnd, insertSize] using hp.1
    have hhalt : Halted (prefixAndUnaryLoop a b xs ys) pEnd := by simpa [pEnd, insertSize] using hp.2
    have htape : pEnd.tape = ⟨word.reverse, .blank, []⟩ := by
      simp [pEnd, sequenceRightConfig, unaryBlockFinish, loopFinalConfig, writerConfig,
        prefixRepeat_left, word, preprocessorWord]
    let endScan : Config 2 := ⟨⟨2, by decide⟩, moveRight ⟨[], .blank, word ++ [.blank]⟩⟩
    have hscan : Reaches scanBack ⟨⟨0, by decide⟩, pEnd.tape⟩ endScan := by
      have h := scanBack_reaches z zs hz hzs
      simpa [htape, he, hw, endScan, List.append_assoc] using h
    have hseq := sequence_complete (prefixAndUnaryLoop a b xs ys) scanBack pStart pEnd endScan
      hstart hhalt hscan (scanBack_halts _)
    simpa [unaryPreprocessor, preprocessorStart, pStart, sequenceLeftConfig, sequenceLeftState,
      shiftPhaseConfig, shiftPhaseState, shiftStart, endScan, prefixLoopSize, insertSize, loopSize] using hseq

#eval (unaryPreprocessor .mark .mark (List.replicate 12 .one) (List.replicate 12 .one)).table.length
#eval (boundedHalt (unaryPreprocessor .mark .mark (List.replicate 12 .one) (List.replicate 12 .one)) 1500
  (preprocessorStart .mark .mark (List.replicate 12 .one) (List.replicate 12 .one) 0)).map
    (fun c => (c.tape.left, c.tape.head, c.tape.right.length))
#print axioms unaryPreprocessor_runs
end LambdaTuring.Machine
