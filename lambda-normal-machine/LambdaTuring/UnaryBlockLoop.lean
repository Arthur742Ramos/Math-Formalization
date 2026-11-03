/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryLoopControl
public meta import LambdaTuring.UnaryLoopControl

@[expose] public section

namespace LambdaTuring.Machine

theorem writeRun_empty_tail (a : Symbol) (xs L : List Symbol) (head : Symbol) :
    writeRun (a :: xs) ⟨L, head, []⟩ = ⟨(a :: xs).reverse ++ L, .blank, []⟩ := by
  induction xs generalizing a L head with
  | nil => rfl
  | cons b xs ih =>
    simpa [writeRun, moveRight, List.reverse_cons, List.append_assoc] using ih b (a :: L) .blank

theorem writeRun_one_blank (a : Symbol) (xs L : List Symbol) :
    writeRun (a :: xs) ⟨L, .one, [.blank]⟩ = ⟨(a :: xs).reverse ++ L, .blank, []⟩ := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    simpa [writeRun, moveRight, List.reverse_cons, List.append_assoc] using
      writeRun_empty_tail b xs (a :: L) .blank

def repeatBlockLeft (block : List Symbol) : Nat → List Symbol → List Symbol
  | 0, L => L
  | n + 1, L => repeatBlockLeft block n (block.reverse ++ L)

theorem repeatBlockLeft_eq (block : List Symbol) (n : Nat) (L : List Symbol) :
    repeatBlockLeft block n L = ((List.replicate n block).flatten).reverse ++ L := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    simp [repeatBlockLeft, ih, List.replicate_succ, List.reverse_append, List.append_assoc]

def unaryBlockLoop (a : Symbol) (xs : List Symbol) :=
  loopProgram (consumeAndInsert a xs) (fixedWriter (a :: xs))

abbrev blockBodySize (a : Symbol) (xs : List Symbol) := 2 + 5 * 12 + 1 + 12 + 1 + 2 * (a :: xs).length + 1
abbrev blockFinalSize (a : Symbol) (xs : List Symbol) := 2 * (a :: xs).length

def unaryBlockStart (a : Symbol) (xs L : List Symbol) (n : Nat) :=
  loopCheckConfig (blockBodySize a xs) (blockFinalSize a xs) ⟨0, by decide⟩
    ⟨L, .one, List.replicate n .one⟩

def unaryBlockFinish (a : Symbol) (xs L : List Symbol) (n : Nat) :=
  loopFinalConfig (n := blockBodySize a xs)
    (writerConfig (a :: xs) (a :: xs).length (by omega)
      ⟨repeatBlockLeft (a :: xs) (n + 1) L, .blank, []⟩)

theorem unaryBlockLoop_runs (a : Symbol) (xs : List Symbol) (hxs : xs.length = 12)
    (L : List Symbol) (n : Nat) :
    Reaches (unaryBlockLoop a xs) (unaryBlockStart a xs L n) (unaryBlockFinish a xs L n) ∧
      Halted (unaryBlockLoop a xs) (unaryBlockFinish a xs L n) := by
  induction n generalizing L with
  | zero =>
    let input : Tape := ⟨L, .one, [.blank]⟩
    let output : Tape := ⟨(a :: xs).reverse ++ L, .blank, []⟩
    let finish := writerConfig (a :: xs) (a :: xs).length (by omega) output
    have hw : Reaches (fixedWriter (a :: xs)) ⟨⟨0, by omega⟩, input⟩ finish := by
      have h := fixedWriter_run (a :: xs) input
      simpa [input, output, finish, writerConfig, writeRun_one_blank] using h
    constructor
    · apply reaches_trans (loop_check_last (consumeAndInsert a xs) (fixedWriter (a :: xs)) L)
      simpa [unaryBlockLoop, unaryBlockStart, unaryBlockFinish, repeatBlockLeft, input, output, finish] using
        loop_final_reaches (consumeAndInsert a xs) (fixedWriter (a :: xs)) _ _ hw
    · simpa [unaryBlockLoop, unaryBlockFinish, repeatBlockLeft, output, finish] using
        loop_final_halt (consumeAndInsert a xs) (fixedWriter (a :: xs)) finish
          (fixedWriter_halts (a :: xs) output)
  | succ n ih =>
    let bodyStart : Config (blockBodySize a xs) :=
      ⟨⟨0, by omega⟩, ⟨L, .one, .one :: List.replicate n .one⟩⟩
    let bodyEnd : Config (blockBodySize a xs) := sequenceRightConfig (n := 76)
      (writerConfig (a :: xs) (a :: xs).length (by omega)
        ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩)
    have hb := consumeAndInsert_runs a xs hxs L n
    have hrun : Reaches (consumeAndInsert a xs) bodyStart bodyEnd := by
      simpa [bodyStart, bodyEnd, consumeStart, sequenceLeftConfig, sequenceLeftState] using hb.1
    have hhalt : Halted (consumeAndInsert a xs) bodyEnd := by simpa [bodyEnd] using hb.2
    constructor
    · apply reaches_trans (loop_check_more (consumeAndInsert a xs) (fixedWriter (a :: xs)) L n)
      apply reaches_trans (loop_body_reaches (consumeAndInsert a xs) (fixedWriter (a :: xs)) _ _ hrun)
      apply Reaches.step (loop_body_halt (consumeAndInsert a xs) (fixedWriter (a :: xs)) bodyEnd hhalt)
      simpa [unaryBlockLoop, unaryBlockStart, unaryBlockFinish, repeatBlockLeft, bodyEnd,
        sequenceRightConfig, writerConfig, blockBodySize, blockFinalSize] using (ih ((a :: xs).reverse ++ L)).1
    · simpa [unaryBlockLoop, unaryBlockFinish, repeatBlockLeft] using
        (ih ((a :: xs).reverse ++ L)).2

#eval (unaryBlockLoop .mark (List.replicate 12 .one)).table.length
#eval (boundedHalt (unaryBlockLoop .mark (List.replicate 12 .one)) 2000
  (unaryBlockStart .mark (List.replicate 12 .one) [] 2)).map
    (fun c => (c.tape.left.length, c.tape.head, c.tape.right))
#print axioms repeatBlockLeft_eq
#print axioms unaryBlockLoop_runs
end LambdaTuring.Machine
