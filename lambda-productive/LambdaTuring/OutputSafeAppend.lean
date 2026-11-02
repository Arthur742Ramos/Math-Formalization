/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputReadAppend
public meta import LambdaTuring.OutputReadAppend

@[expose] public section

namespace LambdaTuring.Machine

/- One known blank separates the unary scratch from arbitrary older tape.
Each append writes into that blank and clears the cell immediately to its
left, re-establishing the invariant without inspecting any farther cells. -/
def safeOutputAppend : Program 8 :=
  ⟨[none, none, some (⟨1, by decide⟩, .left),
    some (⟨1, by decide⟩, .left), none, some (⟨2, by decide⟩, .left),
    some (⟨3, by decide⟩, .write .one), some (⟨2, by decide⟩, .left), none,
    none, some (⟨6, by decide⟩, .left), none,
    none, some (⟨4, by decide⟩, .right), some (⟨5, by decide⟩, .right),
    some (⟨5, by decide⟩, .right), none, none,
    some (⟨7, by decide⟩, .write .blank), some (⟨7, by decide⟩, .write .blank),
      some (⟨7, by decide⟩, .write .blank),
    some (⟨8, by decide⟩, .right), none, none,
    none, some (⟨4, by decide⟩, .right), none]⟩

def safeAppendCfg (q : Fin 9) (L : List Symbol) (a : Symbol) (R : List Symbol) : Config 8 :=
  ⟨q, ⟨L, a, R⟩⟩

theorem safe_append_left_blanks (k : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨1, by decide⟩ (List.replicate k .blank ++ .mark :: L) .blank R)
      (safeAppendCfg ⟨1, by decide⟩ L .mark (List.replicate (k+1) .blank ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨1, by decide⟩ L .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := safeAppendCfg ⟨1, by decide⟩
      (List.replicate k .blank ++ .mark :: L) .blank (.blank :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.blank :: R)

theorem safe_append_left_ones (k : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨2, by decide⟩ (List.replicate k .one ++ .blank :: L) .one R)
      (safeAppendCfg ⟨2, by decide⟩ L .blank (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨2, by decide⟩ L .blank (.one :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := safeAppendCfg ⟨2, by decide⟩
      (List.replicate k .one ++ .blank :: L) .one (.one :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem safe_append_right_ones (k : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨4, by decide⟩ L .one (List.replicate k .one ++ .mark :: R))
      (safeAppendCfg ⟨4, by decide⟩ (List.replicate (k+1) .one ++ L) .mark R) := by
  induction k generalizing L with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨4, by decide⟩ (.one :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := safeAppendCfg ⟨4, by decide⟩ (.one :: L) .one
      (List.replicate k .one ++ .mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: L)

theorem safe_append_right_blanks (k : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨5, by decide⟩ L .blank (List.replicate k .blank ++ .mark :: R))
      (safeAppendCfg ⟨5, by decide⟩ (List.replicate (k+1) .blank ++ L) .mark R) := by
  induction k generalizing L with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨5, by decide⟩ (.blank :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := safeAppendCfg ⟨5, by decide⟩ (.blank :: L) .blank
      (List.replicate k .blank ++ .mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.blank :: L)

theorem safe_append_extend_blank (L R : List Symbol) :
    Reaches safeOutputAppend (safeAppendCfg ⟨3, by decide⟩ L .one R)
      (safeAppendCfg ⟨8, by decide⟩ (.blank :: L.tail) .one R) := by
  cases L with
  | nil =>
    apply Reaches.step (b := safeAppendCfg ⟨6, by decide⟩ [] .blank (.one :: R))
    · rfl
    · exact .step rfl (.step rfl (.refl _))
  | cons a L =>
    cases a <;>
      first | exact .step rfl (.step rfl (.step rfl (.refl _)))

theorem safe_append_seek_mark (gap n : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ .blank :: L)) .mark R)
      (safeAppendCfg ⟨1, by decide⟩ (List.replicate n .one ++ .blank :: L) .mark
        (List.replicate gap .blank ++ .mark :: R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨1, by decide⟩
      (List.replicate n .one ++ .blank :: L) .mark (.mark :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := safeAppendCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ .blank :: L))
      .blank (.mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using safe_append_left_blanks gap (List.replicate n .one ++ .blank :: L) (.mark :: R)

theorem safe_append_find_blank (n : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨1, by decide⟩ (List.replicate n .one ++ .blank :: L) .mark R)
      (safeAppendCfg ⟨2, by decide⟩ L .blank (List.replicate n .one ++ .mark :: R)) := by
  cases n with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨2, by decide⟩ L .blank (.mark :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := safeAppendCfg ⟨2, by decide⟩
      (List.replicate n .one ++ .blank :: L) .one (.mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa using safe_append_left_ones n L (.mark :: R)

theorem safe_append_return_mark (n : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨8, by decide⟩ L .one (List.replicate n .one ++ .mark :: R))
      (safeAppendCfg ⟨4, by decide⟩ (List.replicate (n+1) .one ++ L) .mark R) := by
  cases n with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨4, by decide⟩ (.one :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ n =>
    apply Reaches.step (b := safeAppendCfg ⟨4, by decide⟩ (.one :: L) .one
      (List.replicate n .one ++ .mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using
        safe_append_right_ones n (.one :: L) R

theorem safe_append_return_waypoint (gap : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨4, by decide⟩ L .mark (List.replicate gap .blank ++ .mark :: R))
      (safeAppendCfg ⟨5, by decide⟩ (List.replicate gap .blank ++ .mark :: L) .mark R) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := safeAppendCfg ⟨5, by decide⟩ (.mark :: L) .mark R)
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := safeAppendCfg ⟨5, by decide⟩ (.mark :: L) .blank
      (List.replicate gap .blank ++ .mark :: R))
    · simp [safeOutputAppend, safeAppendCfg, step, instruction, symbolIndex, perform, moveRight,
        List.replicate_succ]
    · simpa using safe_append_right_blanks gap (.mark :: L) R

theorem safeOutputAppend_runs (gap n : Nat) (L R : List Symbol) :
    Reaches safeOutputAppend
      (safeAppendCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate n .one ++ .blank :: L)) .mark R)
      (safeAppendCfg ⟨5, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L.tail)) .mark R) ∧
    Halted safeOutputAppend
      (safeAppendCfg ⟨5, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L.tail)) .mark R) := by
  constructor
  · apply reaches_trans (safe_append_seek_mark gap n L R)
    apply reaches_trans (safe_append_find_blank n L (List.replicate gap Symbol.blank ++ .mark :: R))
    apply Reaches.step (b := safeAppendCfg ⟨3, by decide⟩ L .one
      (List.replicate n .one ++ .mark :: (List.replicate gap .blank ++ .mark :: R)))
    · rfl
    · apply reaches_trans (safe_append_extend_blank L
        (List.replicate n Symbol.one ++ Symbol.mark ::
          (List.replicate gap Symbol.blank ++ Symbol.mark :: R)))
      apply reaches_trans (safe_append_return_mark n (.blank :: L.tail)
        (List.replicate gap Symbol.blank ++ .mark :: R))
      exact safe_append_return_waypoint gap (List.replicate (n+1) .one ++ .blank :: L.tail) R
  · rfl

theorem safeFinish_left_ones (k : Nat) (L R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨3, by decide⟩ (List.replicate k .one ++ .blank :: L) .one R)
      (finishCfg ⟨3, by decide⟩ L .blank (List.replicate (k+1) .one ++ R)) := by
  induction k generalizing R with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨3, by decide⟩ L .blank (.one :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ k ih =>
    apply Reaches.step (b := finishCfg ⟨3, by decide⟩
      (List.replicate k .one ++ .blank :: L) .one (.one :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · simpa [List.replicate_succ, List.append_assoc, replicate_cons_end] using ih (.one :: R)

theorem safeFinish_seek_mark (gap n : Nat) (L R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L)) .blank R)
      (finishCfg ⟨1, by decide⟩ (List.replicate (n+1) .one ++ .blank :: L) .mark
        (List.replicate (gap+1) .blank ++ R)) := by
  cases gap with
  | zero =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate (n+1) .one ++ .blank :: L) .mark (.blank :: R))
    · rfl
    · simpa using Reaches.refl _
  | succ gap =>
    apply Reaches.step (b := finishCfg ⟨1, by decide⟩
      (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L))
      .blank (.blank :: R))
    · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
        List.replicate_succ]
    · have hr : List.replicate (gap+1) Symbol.blank ++ .blank :: R =
          List.replicate (gap+1+1) .blank ++ R := by
        calc
          _ = (List.replicate (gap+1) Symbol.blank ++ [.blank]) ++ R := by simp [List.append_assoc]
          _ = _ := by rw [← List.replicate_succ']
      simpa only [Nat.succ_eq_add_one, hr] using
        finish_left_blanks gap (List.replicate (n+1) .one ++ .blank :: L) (.blank :: R)

theorem safeOutputFinish_runs (gap n : Nat) (L R : List Symbol) :
    Reaches outputFinish
      (finishCfg ⟨0, by decide⟩
        (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L)) .blank R)
      (finishCfg ⟨4, by decide⟩ (.blank :: L) .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) ∧
    Halted outputFinish
      (finishCfg ⟨4, by decide⟩ (.blank :: L) .one
        (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R)) := by
  constructor
  · apply reaches_trans (safeFinish_seek_mark gap n L R)
    apply Reaches.step (b := finishCfg ⟨2, by decide⟩
      (List.replicate (n+1) .one ++ .blank :: L) .blank (List.replicate (gap+1) .blank ++ R))
    · rfl
    · apply Reaches.step (b := finishCfg ⟨3, by decide⟩
        (List.replicate n .one ++ .blank :: L) .one
        (.blank :: (List.replicate (gap+1) .blank ++ R)))
      · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveLeft,
          List.replicate_succ]
      · apply reaches_trans (safeFinish_left_ones n L
          (.blank :: (List.replicate (gap+1) Symbol.blank ++ R)))
        apply Reaches.step (b := finishCfg ⟨4, by decide⟩ (.blank :: L) .one
          (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R))
        · simp [outputFinish, finishCfg, step, instruction, symbolIndex, perform, moveRight,
            List.replicate_succ, List.append_assoc]
        · exact Reaches.refl _
  · rfl

theorem safeOutputFinish_observes (gap n : Nat) (L R : List Symbol) (hR : blanksOnly R = true) :
    ∃ c, Reaches outputFinish
        (finishCfg ⟨0, by decide⟩
          (List.replicate gap .blank ++ .mark :: (List.replicate (n+1) .one ++ .blank :: L)) .blank R) c ∧
      Halted outputFinish c ∧ decode (c.tape.head :: c.tape.right) = some n := by
  refine ⟨finishCfg ⟨4, by decide⟩ (.blank :: L) .one
    (List.replicate n .one ++ List.replicate (gap+2) .blank ++ R), ?_, ?_, ?_⟩
  · exact (safeOutputFinish_runs gap n L R).1
  · exact (safeOutputFinish_runs gap n L R).2
  · exact outputFinish_decodes gap n R hR

#print axioms safe_append_extend_blank
#print axioms safeOutputAppend_runs
#print axioms safeOutputFinish_observes
end LambdaTuring.Machine
