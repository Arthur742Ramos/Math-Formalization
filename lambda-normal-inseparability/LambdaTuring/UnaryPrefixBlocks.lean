/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryBlockLoop
public meta import LambdaTuring.UnaryBlockLoop

@[expose] public section

namespace LambdaTuring.Machine

/-- Insert a fixed prefix block, then replace each cell in the unary run by
another fixed block. The output head is on the blank following the blocks. -/
def prefixAndUnaryLoop (a b : Symbol) (xs ys : List Symbol) :=
  sequenceProgram (insertBlock a xs) (unaryBlockLoop b ys)

theorem prefixAndUnaryLoop_runs (a b : Symbol) (xs ys : List Symbol)
    (hxs : xs.length = 12) (hys : ys.length = 12) (L : List Symbol) (n : Nat) :
    let start := sequenceLeftConfig (sequenceLeftConfig (sequenceLeftConfig
      (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart L n))))
    let finish := sequenceRightConfig (unaryBlockFinish b ys ((a :: xs).reverse ++ L) n)
    Reaches (prefixAndUnaryLoop a b xs ys) start finish ∧
      Halted (prefixAndUnaryLoop a b xs ys) finish := by
  let firstStart := sequenceLeftConfig (n := 78) (m := 2 * (a :: xs).length)
    (sequenceLeftConfig (n := 65) (m := 12)
      (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart L n)))
  let firstEnd := sequenceRightConfig (n := 78)
    (writerConfig (a :: xs) (a :: xs).length (by omega)
      ⟨(a :: xs).reverse ++ L, .one, List.replicate n .one⟩)
  have hfirst := insertBlock_runs a xs hxs L n
  have hrun : Reaches (insertBlock a xs) firstStart firstEnd := by
    simpa [firstStart, firstEnd] using hfirst.1
  have hhalt : Halted (insertBlock a xs) firstEnd := by simpa [firstEnd] using hfirst.2
  have hsecond := unaryBlockLoop_runs b ys hys ((a :: xs).reverse ++ L) n
  have hrun2 : Reaches (unaryBlockLoop b ys) ⟨⟨0, by omega⟩, firstEnd.tape⟩
      (unaryBlockFinish b ys ((a :: xs).reverse ++ L) n) := by
    simpa [firstEnd, sequenceRightConfig, writerConfig, unaryBlockStart,
      loopCheckConfig, loopControlState] using hsecond.1
  exact sequence_complete (insertBlock a xs) (unaryBlockLoop b ys) firstStart firstEnd _
    hrun hhalt hrun2 hsecond.2

theorem prefixRepeat_left (pre block L : List Symbol) (n : Nat) :
    repeatBlockLeft block n (pre.reverse ++ L) =
      (pre ++ (List.replicate n block).flatten).reverse ++ L := by
  simp [repeatBlockLeft_eq, List.reverse_append, List.append_assoc]

#print axioms prefixAndUnaryLoop_runs
#print axioms prefixRepeat_left
end LambdaTuring.Machine
