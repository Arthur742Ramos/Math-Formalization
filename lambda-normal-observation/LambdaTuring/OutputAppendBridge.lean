/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputMarkBlock
public meta import LambdaTuring.OutputMarkBlock

@[expose] public section

namespace LambdaTuring.Machine

theorem listBlank_nonblank_end (pre ys : List Symbol) (a : Symbol) (ha : a ≠ .blank)
    (h : Turing.ListBlank.mk (pre ++ [a]) = Turing.ListBlank.mk ys) :
    ∃ z, ys = (pre ++ [a]) ++ List.replicate z .blank := by
  have hr : Turing.BlankRel (pre ++ [a]) ys := Quotient.exact h
  cases hr with
  | inl h =>
    rcases h with ⟨z, hz⟩
    exact ⟨z, hz⟩
  | inr h =>
    rcases h with ⟨z, hz⟩
    cases z with
    | zero =>
      refine ⟨0, ?_⟩
      simpa using hz.symm
    | succ z =>
      have hl := congrArg List.getLast? hz
      simp [List.getLast?_append, List.getLast?_replicate] at hl
      exact (ha hl).elim

theorem scratch_representative (gap n : Nat) (ys : List Symbol)
    (h : Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one) =
      Turing.ListBlank.mk ys) :
    ∃ z, ys = (List.replicate gap .blank ++ .mark :: List.replicate n .one) ++
      List.replicate z .blank := by
  cases n with
  | zero =>
    have hh : Turing.ListBlank.mk (List.replicate gap .blank ++ [.mark]) = Turing.ListBlank.mk ys := by
      simpa using h
    obtain ⟨z, hz⟩ := listBlank_nonblank_end _ ys .mark (by decide) hh
    refine ⟨z, ?_⟩
    simpa using hz
  | succ n =>
    have hcanon : List.replicate gap Symbol.blank ++ .mark :: List.replicate (n+1) .one =
        (List.replicate gap .blank ++ .mark :: List.replicate n .one) ++ [.one] := by
      rw [List.replicate_succ']
      simp [List.append_assoc]
    rw [hcanon] at h
    obtain ⟨z, hz⟩ := listBlank_nonblank_end _ ys .one (by decide) h
    refine ⟨z, ?_⟩
    simpa [← hcanon] using hz

theorem outputAppend_from_quotient (t : Tape) (gap n : Nat) (R : Turing.ListBlank Symbol)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (R.cons .mark)) :
    ∃ d, Reaches outputAppend ⟨⟨0, by decide⟩, t⟩ d ∧ Halted outputAppend d ∧
      mathTape d.tape = Turing.Tape.mk'
        (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one))
        (R.cons .mark) := by
  have hh : t.head = .mark := by
    have h := congrArg Turing.Tape.head ht
    simpa [mathTape, Turing.Tape.mk'] using h
  have hl : Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one) =
      Turing.ListBlank.mk t.left := by
    have h := congrArg Turing.Tape.left ht
    simpa [mathTape, Turing.Tape.mk'] using h.symm
  have hr : Turing.ListBlank.mk t.right = R := by
    have h := congrArg Turing.Tape.right ht
    simpa [mathTape, Turing.Tape.mk'] using h
  obtain ⟨z, hz⟩ := scratch_representative gap n t.left hl
  let d := appendCfg ⟨5, by decide⟩
    (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ List.replicate (z-1) .blank))
    .mark t.right
  refine ⟨d, ?_, ?_, ?_⟩
  · have h := (outputAppend_with_left_blanks gap n z t.right).1
    cases t with
    | mk left head right =>
      simp only at hh hz
      subst head
      subst left
      simpa [d, appendCfg, List.append_assoc] using h
  · exact (outputAppend_with_left_blanks gap n z t.right).2
  · have hext :
        Turing.ListBlank.mk ((List.replicate gap Symbol.blank ++ Symbol.mark :: List.replicate (n+1) Symbol.one) ++
          List.replicate (z-1) Symbol.blank) =
        Turing.ListBlank.mk (List.replicate gap Symbol.blank ++ Symbol.mark :: List.replicate (n+1) Symbol.one) := by
      apply Quotient.sound
      exact Or.inr ⟨z-1, rfl⟩
    simp only [d, appendCfg, mathTape, Turing.Tape.mk', Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
    rw [hr]
    congr 1
    simpa only [List.append_assoc, List.cons_append] using hext

def markAndAppend := sequenceProgram markOutputBlock outputAppend

/- After the source cell's main-track value has been read, replace its block
by a waypoint and append one unary cell. The unprocessed source tail remains
unchanged and the head returns to the waypoint. -/
set_option backward.isDefEq.respectTransparency false in
theorem markAndAppend_runs (t : Tape) (gap n : Nat) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (encodeBlankSide R)) :
    ∃ d, Reaches markAndAppend (sequenceLeftConfig
        (n := 2 * waypointBlock.length + 13 + 1) (m := 5)
        (sequenceLeftConfig (n := 2 * waypointBlock.length) (m := 13)
          (writerConfig waypointBlock 0 (by omega) t))) d ∧
      Halted markAndAppend d ∧
      mathTape d.tape = Turing.Tape.mk'
        (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one))
        (Turing.ListBlank.append waypointBlock (encodeBlankSide R.tail)) := by
  obtain ⟨mid, hrun, hhalt, hmid⟩ := markOutputBlock_runs t
    (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one)) R ht
  let tail := Turing.ListBlank.append (List.replicate 12 Symbol.blank) (encodeBlankSide R.tail)
  have ht' : mathTape mid.tape = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (tail.cons .mark) := by
    simpa [waypointBlock, Turing.ListBlank.append, tail] using hmid
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ := outputAppend_from_quotient mid.tape gap n tail ht'
  have hs := sequence_complete markOutputBlock outputAppend
    (sequenceLeftConfig (writerConfig waypointBlock 0 (by omega) t)) mid out
    hrun hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig (n := 2 * waypointBlock.length + 13 + 1) (m := 5) out,
    hs.1, hs.2, ?_⟩
  simpa [sequenceRightConfig, waypointBlock, Turing.ListBlank.append, tail] using hout

def clearWaypoint := fixedWriter (List.replicate 13 .blank)

theorem clearWaypoint_runs (t : Tape) (L : Turing.ListBlank Symbol) (R : Turing.ListBlank Symbol)
    (ht : mathTape t = Turing.Tape.mk' L (Turing.ListBlank.append waypointBlock R)) :
    ∃ d, Reaches clearWaypoint ⟨⟨0, by omega⟩, t⟩ d ∧ Halted clearWaypoint d ∧
      mathTape d.tape = Turing.Tape.mk' (Turing.ListBlank.append (List.replicate 13 .blank) L) R := by
  let xs := List.replicate 13 Symbol.blank
  let d := writerConfig xs xs.length (by omega) (writeRun xs t)
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa [clearWaypoint, xs, d, writerConfig] using fixedWriter_run xs t
  · exact fixedWriter_halts xs _
  · change mathTape (writeRun xs t) = _
    rw [mathTape_writeRun, ht]
    have hlen : xs.length = waypointBlock.length := by simp [xs, waypointBlock_length]
    rw [writeBlock_list xs waypointBlock L R hlen]
    simp [xs]

def markAppendNext := sequenceProgram markAndAppend clearWaypoint

set_option backward.isDefEq.respectTransparency false in
theorem markAppendNext_runs (t : Tape) (gap n : Nat) (R : Turing.ListBlank SimAlphabet)
    (ht : mathTape t = Turing.Tape.mk'
      (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate n .one))
      (encodeBlankSide R)) :
    ∃ d, Reaches markAppendNext ⟨⟨0, by omega⟩, t⟩ d ∧ Halted markAppendNext d ∧
      mathTape d.tape = Turing.Tape.mk'
        (Turing.ListBlank.mk (List.replicate (13+gap) .blank ++ .mark :: List.replicate (n+1) .one))
        (encodeBlankSide R.tail) := by
  obtain ⟨mid, hrun, hhalt, hmid⟩ := markAndAppend_runs t gap n R ht
  have hrun' : Reaches markAndAppend ⟨⟨0, by omega⟩, t⟩ mid := by
    simpa [sequenceLeftConfig, sequenceLeftState, writerConfig] using hrun
  obtain ⟨out, hrun₂, hhalt₂, hout⟩ := clearWaypoint_runs mid.tape
    (Turing.ListBlank.mk (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one))
    (encodeBlankSide R.tail) hmid
  have hs := sequence_complete markAndAppend clearWaypoint ⟨⟨0, by omega⟩, t⟩ mid out
    hrun' hhalt hrun₂ hhalt₂
  refine ⟨sequenceRightConfig out, hs.1, hs.2, ?_⟩
  change mathTape out.tape = _
  rw [hout, Turing.ListBlank.append_mk]
  congr 2
  rw [← List.append_assoc, ← List.replicate_add]

#print axioms scratch_representative
#print axioms outputAppend_from_quotient
#print axioms markAndAppend_runs
#print axioms markAppendNext_runs
end LambdaTuring.Machine
