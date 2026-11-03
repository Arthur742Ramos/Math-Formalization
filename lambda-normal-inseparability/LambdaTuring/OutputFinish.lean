/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputAppend
public meta import LambdaTuring.OutputAppend

@[expose] public section

namespace LambdaTuring.Machine

/- Starting to the right of a blank gap, erase the boundary marker and
place the head at the left end of the nonempty unary output. -/
def outputFinish : Program 4 :=
  ⟨[some (⟨1, by decide⟩, .left), none, none,
    some (⟨1, by decide⟩, .left), none, some (⟨2, by decide⟩, .write .blank),
    some (⟨3, by decide⟩, .left), none, none,
    some (⟨4, by decide⟩, .right), some (⟨3, by decide⟩, .left), none]⟩

def finishCfg (q : Fin 5) (L : List Symbol) (a : Symbol) (R : List Symbol) : Config 4 :=
  ⟨q, ⟨L, a, R⟩⟩

theorem finish_left_blanks (k : Nat) (L R : List Symbol) :
    Reaches outputFinish (finishCfg ⟨1, by decide⟩ (List.replicate k .blank ++ .mark :: L) .blank R)
      (finishCfg ⟨1, by decide⟩ L .mark (List.replicate (k+1) .blank ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩ L .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate k .blank ++ .mark :: L) .blank (.blank :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.blank :: R)

theorem finish_left_ones (k : Nat) (R : List Symbol) :
    Reaches outputFinish (finishCfg ⟨3, by decide⟩ (List.replicate k .one) .one R)
      (finishCfg ⟨3, by decide⟩ [] .blank (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨3, by decide⟩ [] .blank (.one :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := finishCfg ⟨3, by decide⟩ (List.replicate k .one) .one (.one :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem finish_seek_mark (gap n : Nat) (R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .blank R)
      (finishCfg ⟨1, by decide⟩ (List.replicate (n+1) .one) .mark
        (List.replicate (gap+1) .blank ++ R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩ (List.replicate (n+1) .one) .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .blank (.blank :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using
        finish_left_blanks gap (List.replicate (n+1) .one) (.blank :: R)

theorem outputFinish_runs (gap n : Nat) (R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .blank R)
      (finishCfg ⟨4, by decide⟩ [.blank] .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) ∧
    Halted outputFinish
      (finishCfg ⟨4, by decide⟩ [.blank] .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) := by
  constructor
  · apply reaches_trans (finish_seek_mark gap n R)
    apply Reaches.step (b := finishCfg ⟨2, by decide⟩ (List.replicate (n+1) .one) .blank
      (List.replicate (gap+1) .blank ++ R))
    · rfl
    · apply Reaches.step (b := finishCfg ⟨3, by decide⟩ (List.replicate n .one) .one
        (.blank :: (List.replicate (gap+1) .blank ++ R)))
      · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · apply reaches_trans (finish_left_ones n (.blank :: (List.replicate (gap+1) Symbol.blank ++ R)))
        apply Reaches.step (b := finishCfg ⟨4, by decide⟩ [.blank] .one
          (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R))
        · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveRight,
            List.replicate_succ, List.append_assoc]
        · exact Reaches.refl _
  · rfl

theorem blanksOnly_eq_replicate (R : List Symbol) (h : blanksOnly R = true) :
    R = List.replicate R.length .blank := by
  induction R with
  | nil => rfl
  | cons a R ih =>
    cases a with
    | blank =>
      change blanksOnly R = true at h
      simp only [List.length_cons, List.replicate_succ]
      congr 1
      exact ih h
    | one => simp [blanksOnly] at h
    | mark => simp [blanksOnly] at h

theorem outputFinish_decodes (gap n : Nat) (R : List Symbol) (hR : blanksOnly R = true) :
    decode ((finishCfg ⟨4, by decide⟩ [.blank] .one
      (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)).tape.head ::
      (finishCfg ⟨4, by decide⟩ [.blank] .one
      (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)).tape.right) = some n := by
  have h := blanksOnly_eq_replicate R hR
  conv_lhs => rw [h]
  change decode (.one :: (List.replicate n .one ++ List.replicate (gap+2) .blank ++
    List.replicate R.length .blank)) = some n
  have heq : .one :: (List.replicate n .one ++ List.replicate (gap+2) .blank ++
      List.replicate R.length .blank) =
      input n ++ List.replicate (gap+2+R.length) .blank := by
    simp only [input, List.replicate_add, List.replicate_succ, List.cons_append, List.append_assoc]
  rw [heq, decode_append_blanks, decode_input]

theorem outputFinish_observes (gap n : Nat) (R : List Symbol) (hR : blanksOnly R = true) :
    ∃ c, Reaches outputFinish
        (finishCfg ⟨0, by decide⟩ (List.replicate gap .blank ++ .mark :: List.replicate (n+1) .one) .blank R) c ∧
      Halted outputFinish c ∧ decode (c.tape.head :: c.tape.right) = some n := by
  refine ⟨finishCfg ⟨4, by decide⟩ [.blank] .one
    (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R), ?_, ?_, ?_⟩
  · exact (outputFinish_runs gap n R).1
  · exact (outputFinish_runs gap n R).2
  · exact outputFinish_decodes gap n R hR

theorem finish_left_ones_with_tail (k z : Nat) (R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨3, by decide⟩ (List.replicate k .one ++ List.replicate z .blank) .one R)
      (finishCfg ⟨3, by decide⟩ (List.replicate (z-1) .blank) .blank
        (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    cases z with
    | zero =>
      apply Reaches.step (b := finishCfg ⟨3, by decide⟩ [] .blank (.one :: R))
      · rfl
      · simpa using Reaches.refl _
    | succ z =>
      apply Reaches.step (b := finishCfg ⟨3, by decide⟩ (List.replicate z .blank) .blank (.one :: R))
      · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := finishCfg ⟨3, by decide⟩
      (List.replicate k .one ++ List.replicate z .blank) .one (.one :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem finish_seek_mark_with_tail (gap n z : Nat) (R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ List.replicate z .blank))
        .blank R)
      (finishCfg ⟨1, by decide⟩ (List.replicate (n+1) .one ++ List.replicate z .blank) .mark
        (List.replicate (gap+1) .blank ++ R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate (n+1) .one ++ List.replicate z .blank) .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ List.replicate z .blank))
      .blank (.blank :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · have hr : List.replicate (gap+1) Symbol.blank ++ .blank :: R =
          List.replicate (gap+1+1) .blank ++ R := by
        calc
          _ = (List.replicate (gap+1) Symbol.blank ++ [.blank]) ++ R := by simp [List.append_assoc]
          _ = _ := by rw [← List.replicate_succ']
      simpa only [Nat.succ_eq_add_one, hr] using
        finish_left_blanks gap (List.replicate (n+1) .one ++ List.replicate z .blank) (.blank :: R)

theorem outputFinish_with_left_blanks (gap n z : Nat) (R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ List.replicate z .blank))
        .blank R)
      (finishCfg ⟨4, by decide⟩ (.blank :: List.replicate (z-1) .blank) .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) ∧
    Halted outputFinish
      (finishCfg ⟨4, by decide⟩ (.blank :: List.replicate (z-1) .blank) .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) := by
  constructor
  · apply reaches_trans (finish_seek_mark_with_tail gap n z R)
    apply Reaches.step (b := finishCfg ⟨2, by decide⟩
      (List.replicate (n+1) .one ++ List.replicate z .blank) .blank
      (List.replicate (gap+1) .blank ++ R))
    · rfl
    · apply Reaches.step (b := finishCfg ⟨3, by decide⟩
        (List.replicate n .one ++ List.replicate z .blank) .one
        (.blank :: (List.replicate (gap+1) .blank ++ R)))
      · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · apply reaches_trans (finish_left_ones_with_tail n z
          (.blank :: (List.replicate (gap+1) Symbol.blank ++ R)))
        apply Reaches.step (b := finishCfg ⟨4, by decide⟩ (.blank :: List.replicate (z-1) .blank) .one
          (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R))
        · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveRight,
            List.replicate_succ, List.append_assoc]
        · exact Reaches.refl _
  · rfl

theorem outputFinish_observes_with_blank_extensions
    (gap n : Nat) (L R : List Symbol) (hL : blanksOnly L = true) (hR : blanksOnly R = true) :
    ∃ c, Reaches outputFinish
        (finishCfg ⟨0, by decide⟩
          (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ L)) .blank R) c ∧
      Halted outputFinish c ∧ decode (c.tape.head :: c.tape.right) = some n := by
  have heq := blanksOnly_eq_replicate L hL
  rw [heq]
  refine ⟨finishCfg ⟨4, by decide⟩ (.blank :: List.replicate (L.length-1) .blank) .one
    (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R), ?_, ?_, ?_⟩
  · exact (outputFinish_with_left_blanks gap n L.length R).1
  · exact (outputFinish_with_left_blanks gap n L.length R).2
  · exact outputFinish_decodes gap n R hR

#print axioms outputFinish_runs
#print axioms outputFinish_decodes
#print axioms outputFinish_observes
#print axioms outputFinish_with_left_blanks
#print axioms outputFinish_observes_with_blank_extensions
end LambdaTuring.Machine
