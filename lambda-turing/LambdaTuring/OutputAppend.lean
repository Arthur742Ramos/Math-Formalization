/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MainTrackMachine
public meta import LambdaTuring.MainTrackMachine
public import LambdaTuring.UnaryShift
public meta import LambdaTuring.UnaryShift

@[expose] public section

namespace LambdaTuring.Machine

/- The two marks delimit a blank gap. The unary output lies to the left of
the left mark. Starting at the right mark, append one cell on the left and
return to that mark, leaving the gap and all data to its right unchanged. -/
def outputAppend : Program 5 :=
  ⟨[none, none, some (⟨1, by decide⟩, .left),
    some (⟨1, by decide⟩, .left), none, some (⟨2, by decide⟩, .left),
    some (⟨3, by decide⟩, .write .one), some (⟨2, by decide⟩, .left), none,
    none, some (⟨4, by decide⟩, .right), none,
    none, some (⟨4, by decide⟩, .right), some (⟨5, by decide⟩, .right),
    some (⟨5, by decide⟩, .right), none, none]⟩

def appendCfg (q : Fin 6) (L : List Symbol) (a : Symbol) (R : List Symbol) : Config 5 :=
  ⟨q, ⟨L, a, R⟩⟩

theorem replicate_cons_end (a : Symbol) (k : Nat) (R : List Symbol) :
    List.replicate k a ++ a :: R = a :: (List.replicate k a ++ R) := by
  have h := congrArg (fun xs : List Symbol => xs ++ R)
    (List.replicate_succ' (n := k) (a := a)).symm
  simpa [List.replicate_succ, List.append_assoc] using h

theorem append_left_blanks (k : Nat) (L R : List Symbol) :
    Reaches outputAppend (appendCfg ⟨1, by decide⟩ (List.replicate k .blank ++ .mark :: L) .blank R)
      (appendCfg ⟨1, by decide⟩ L .mark (List.replicate (k+1) .blank ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩ L .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩
      (List.replicate k .blank ++ .mark :: L) .blank (.blank :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.blank :: R)

theorem append_left_ones (k : Nat) (R : List Symbol) :
    Reaches outputAppend (appendCfg ⟨2, by decide⟩ (List.replicate k .one) .one R)
      (appendCfg ⟨2, by decide⟩ [] .blank (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩ [] .blank (.one :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩ (List.replicate k .one) .one (.one :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem append_right_ones (k : Nat) (L R : List Symbol) :
    Reaches outputAppend (appendCfg ⟨4, by decide⟩ L .one (List.replicate k .one ++ .mark :: R))
      (appendCfg ⟨4, by decide⟩ (List.replicate (k+1) .one ++ L) .mark R) := by
  induction k generalizing L with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ (.one :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ (.one :: L) .one
      (List.replicate k .one ++ .mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: L)

theorem append_right_blanks (k : Nat) (L R : List Symbol) :
    Reaches outputAppend (appendCfg ⟨5, by decide⟩ L .blank (List.replicate k .blank ++ .mark :: R))
      (appendCfg ⟨5, by decide⟩ (List.replicate (k+1) .blank ++ L) .mark R) := by
  induction k generalizing L with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨5, by decide⟩ (.blank :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := appendCfg ⟨5, by decide⟩ (.blank :: L) .blank
      (List.replicate k .blank ++ .mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.blank :: L)

theorem append_seek_mark (gap n : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨0, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate n .one) .mark R)
      (appendCfg ⟨1, by decide⟩ (List.replicate n .one) .mark
        (List.replicate gap .blank ++ .mark :: R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩ (List.replicate n .one) .mark (.mark :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: List.replicate n .one) .blank (.mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using append_left_blanks gap (List.replicate n .one) (.mark :: R)

theorem append_find_blank (n : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨1, by decide⟩ (List.replicate n .one) .mark R)
      (appendCfg ⟨2, by decide⟩ [] .blank (List.replicate n .one ++ .mark :: R)) := by
  cases n with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩ [] .blank (.mark :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩ (List.replicate n .one) .one (.mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using append_left_ones n (.mark :: R)

theorem append_return_mark (n : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨3, by decide⟩ [] .one (List.replicate n .one ++ .mark :: R))
      (appendCfg ⟨4, by decide⟩ (List.replicate (n+1) .one) .mark R) := by
  cases n with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ [.one] .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ [.one] .one
      (List.replicate n .one ++ .mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using
        append_right_ones n [.one] R

theorem append_return_waypoint (gap : Nat) (L R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨4, by decide⟩ L .mark (List.replicate gap .blank ++ .mark :: R))
      (appendCfg ⟨5, by decide⟩ (List.replicate gap .blank ++ .mark :: L) .mark R) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨5, by decide⟩ (.mark :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := appendCfg ⟨5, by decide⟩ (.mark :: L) .blank
      (List.replicate gap .blank ++ .mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa using append_right_blanks gap (.mark :: L) R

theorem outputAppend_runs (gap n : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨0, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate n .one) .mark R)
      (appendCfg ⟨5, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .mark R) ∧
    Halted outputAppend
      (appendCfg ⟨5, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .mark R) := by
  constructor
  · apply reaches_trans (append_seek_mark gap n R)
    apply reaches_trans (append_find_blank n (List.replicate gap Symbol.blank ++ .mark :: R))
    apply Reaches.step (b := appendCfg ⟨3, by decide⟩ [] .one
      (List.replicate n .one ++ .mark :: (List.replicate gap .blank ++ .mark :: R)))
    · rfl
    · apply reaches_trans (append_return_mark n (List.replicate gap Symbol.blank ++ .mark :: R))
      exact append_return_waypoint gap (List.replicate (n+1) .one) R
  · rfl

theorem append_left_ones_with_tail (k z : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨2, by decide⟩ (List.replicate k .one ++ List.replicate z .blank) .one R)
      (appendCfg ⟨2, by decide⟩ (List.replicate (z-1) .blank) .blank
        (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    cases z with
    | zero =>
      apply Reaches.step (b := appendCfg ⟨2, by decide⟩ [] .blank (.one :: R))
      · rfl
      · simpa using Reaches.refl _
    | succ z =>
      apply Reaches.step (b := appendCfg ⟨2, by decide⟩ (List.replicate z .blank) .blank (.one :: R))
      · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩
      (List.replicate k .one ++ List.replicate z .blank) .one (.one :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem append_seek_mark_with_tail (gap n z : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ List.replicate z .blank))
        .mark R)
      (appendCfg ⟨1, by decide⟩ (List.replicate n .one ++ List.replicate z .blank) .mark
        (List.replicate gap .blank ++ .mark :: R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩
      (List.replicate n .one ++ List.replicate z .blank) .mark (.mark :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := appendCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ List.replicate z .blank))
      .blank (.mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using append_left_blanks gap (List.replicate n .one ++ List.replicate z .blank) (.mark :: R)

theorem append_find_blank_with_tail (n z : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨1, by decide⟩ (List.replicate n .one ++ List.replicate z .blank) .mark R)
      (appendCfg ⟨2, by decide⟩ (List.replicate (z-1) .blank) .blank
        (List.replicate n .one ++ .mark :: R)) := by
  cases n with
  | zero =>
    cases z with
    | zero =>
      apply Reaches.step (b := appendCfg ⟨2, by decide⟩ [] .blank (.mark :: R))
      · rfl
      · simpa using Reaches.refl _
    | succ z =>
      apply Reaches.step (b := appendCfg ⟨2, by decide⟩ (List.replicate z .blank) .blank (.mark :: R))
      · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := appendCfg ⟨2, by decide⟩
      (List.replicate n .one ++ List.replicate z .blank) .one (.mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using append_left_ones_with_tail n z (.mark :: R)

theorem append_return_mark_with_tail (n : Nat) (L R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨3, by decide⟩ L .one (List.replicate n .one ++ .mark :: R))
      (appendCfg ⟨4, by decide⟩ (List.replicate (n+1) .one ++ L) .mark R) := by
  cases n with
  | zero =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ (.one :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := appendCfg ⟨4, by decide⟩ (.one :: L) .one
      (List.replicate n .one ++ .mark :: R))
    · simp [outputAppend, appendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using
        append_right_ones n (.one :: L) R

theorem outputAppend_with_left_blanks (gap n z : Nat) (R : List Symbol) :
    Reaches outputAppend
      (appendCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ List.replicate z .blank))
        .mark R)
      (appendCfg ⟨5, by decide⟩
        (List.replicate gap .blank ++ .mark ::
          (List.replicate (n+1) .one ++ List.replicate (z-1) .blank)) .mark R) ∧
    Halted outputAppend
      (appendCfg ⟨5, by decide⟩
        (List.replicate gap .blank ++ .mark ::
          (List.replicate (n+1) .one ++ List.replicate (z-1) .blank)) .mark R) := by
  constructor
  · apply reaches_trans (append_seek_mark_with_tail gap n z R)
    apply reaches_trans (append_find_blank_with_tail n z (List.replicate gap Symbol.blank ++ .mark :: R))
    apply Reaches.step (b := appendCfg ⟨3, by decide⟩ (List.replicate (z-1) .blank) .one
      (List.replicate n .one ++ .mark :: (List.replicate gap .blank ++ .mark :: R)))
    · rfl
    · apply reaches_trans (append_return_mark_with_tail n (List.replicate (z-1) .blank)
        (List.replicate gap Symbol.blank ++ .mark :: R))
      exact append_return_waypoint gap (List.replicate (n+1) .one ++ List.replicate (z-1) .blank) R
  · rfl

#print axioms append_left_blanks
#print axioms append_left_ones
#print axioms append_right_ones
#print axioms append_right_blanks
#print axioms outputAppend_runs
#print axioms outputAppend_with_left_blanks
end LambdaTuring.Machine
