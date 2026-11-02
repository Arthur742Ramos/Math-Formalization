/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable

@[expose] public section

namespace LambdaTuring.Machine

/-- Write a fixed finite block, moving right after each cell. -/
def fixedWriterInstruction (xs : List Symbol) (q : Fin (2 * xs.length + 1)) (_ : Symbol) :
    Option (Fin (2 * xs.length + 1) × Action) := by
  if h : q.val < 2 * xs.length then
    let next : Fin (2 * xs.length + 1) := ⟨q.val + 1, by omega⟩
    if q.val % 2 = 0 then
      exact (xs[q.val / 2]?).map fun a => (next, .write a)
    else exact some (next, .right)
  else exact none

def fixedWriter (xs : List Symbol) : Program (2 * xs.length) :=
  tableOfFunction (fixedWriterInstruction xs)

def writeRun : List Symbol → Tape → Tape
  | [], t => t
  | a :: xs, t => writeRun xs (moveRight { t with head := a })

def writerConfig (xs : List Symbol) (i : Nat) (h : i ≤ xs.length) (t : Tape) :
    Config (2 * xs.length) := ⟨⟨2 * i, by omega⟩, t⟩

theorem fixedWriter_write (xs : List Symbol) (i : Nat) (h : i < xs.length) (t : Tape) :
    step (fixedWriter xs) (writerConfig xs i (Nat.le_of_lt h) t) =
      some ⟨⟨2 * i + 1, by omega⟩, { t with head := xs[i] }⟩ := by
  simp only [step, fixedWriter, tableOfFunction_instruction, writerConfig]
  unfold fixedWriterInstruction
  have hb : 2 * i < 2 * xs.length := by omega
  rw [dite_eq_left hb]
  simp [h, perform]

theorem fixedWriter_move (xs : List Symbol) (i : Nat) (h : i < xs.length) (t : Tape) :
    step (fixedWriter xs) ⟨⟨2 * i + 1, by omega⟩, t⟩ =
      some (writerConfig xs (i + 1) (by omega) (moveRight t)) := by
  simp only [step, fixedWriter, tableOfFunction_instruction]
  unfold fixedWriterInstruction
  have hb : 2 * i + 1 < 2 * xs.length := by omega
  rw [dite_eq_left hb]
  simp [writerConfig, perform, Nat.mul_add]

theorem fixedWriter_halts (xs : List Symbol) (t : Tape) :
    Halted (fixedWriter xs) (writerConfig xs xs.length (by omega) t) := by
  simp [Halted, step, fixedWriter, tableOfFunction_instruction, writerConfig,
    fixedWriterInstruction]

theorem fixedWriter_runs (xs pre suffix : List Symbol) (heq : xs = pre ++ suffix) (t : Tape) :
    Reaches (fixedWriter xs)
      (writerConfig xs pre.length (by rw [heq]; simp) t)
      (writerConfig xs (pre.length + suffix.length) (by rw [heq]; simp)
        (writeRun suffix t)) := by
  induction suffix generalizing pre t with
  | nil => simp [writeRun]; exact .refl _
  | cons a rest ih =>
    have h : pre.length < xs.length := by rw [heq]; simp
    have ha? : xs[pre.length]? = some a := by simp [heq]
    have ha : xs[pre.length] = a := by simpa [List.getElem?_eq_getElem h] using ha?
    have hw := fixedWriter_write xs pre.length h t
    have hm := fixedWriter_move xs pre.length h { t with head := a }
    rw [ha] at hw
    apply Reaches.step hw
    apply Reaches.step hm
    have heq' : xs = (pre ++ [a]) ++ rest := by simpa [List.append_assoc] using heq
    have next := ih (pre ++ [a]) heq' (moveRight { t with head := a })
    simpa [writeRun, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem fixedWriter_run (xs : List Symbol) (t : Tape) :
    Reaches (fixedWriter xs) (writerConfig xs 0 (by omega) t)
      (writerConfig xs xs.length (by omega) (writeRun xs t)) := by
  simpa using fixedWriter_runs xs [] xs rfl t

theorem writeRun_blank_cells (a : Symbol) (xs L R : List Symbol) (r : Symbol) :
    writeRun (a :: xs) ⟨L, .blank, List.replicate xs.length .blank ++ r :: R⟩ =
      ⟨(a :: xs).reverse ++ L, r, R⟩ := by
  induction xs generalizing a L with
  | nil => rfl
  | cons b xs ih =>
    simpa [writeRun, moveRight, List.replicate_succ, List.reverse_cons, List.append_assoc] using
      ih b (a :: L)

#eval (fixedWriter (List.replicate 13 .mark)).table.length
#print axioms fixedWriter_run
#print axioms fixedWriter_halts
#print axioms writeRun_blank_cells
end LambdaTuring.Machine
