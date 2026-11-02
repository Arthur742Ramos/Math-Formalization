/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineCompilerBase
public meta import LambdaTuring.MachineCompilerBase

@[expose] public section

namespace LambdaTuring.Machine

/-- Move left across a nonblank word, then return to its first cell. -/
def scanBack : Program 2 :=
  ⟨[some (⟨1, by decide⟩, .left), some (⟨1, by decide⟩, .left),
    some (⟨1, by decide⟩, .left),
    some (⟨2, by decide⟩, .right), some (⟨1, by decide⟩, .left),
    some (⟨1, by decide⟩, .left)]⟩

def scanCfg (left : List Symbol) (head : Symbol) (right : List Symbol) : Config 2 :=
  ⟨⟨1, by decide⟩, ⟨left, head, right⟩⟩

theorem scan_nonblank_next (a b : Symbol) (left right : List Symbol) (ha : a ≠ .blank) :
    step scanBack (scanCfg (b :: left) a right) = some (scanCfg left b (a :: right)) := by
  cases a <;> simp_all [scanBack, scanCfg, step, instruction, symbolIndex, perform, moveLeft]

theorem scan_nonblank_last (a : Symbol) (right : List Symbol) (ha : a ≠ .blank) :
    step scanBack (scanCfg [] a right) = some (scanCfg [] .blank (a :: right)) := by
  cases a <;> simp_all [scanBack, scanCfg, step, instruction, symbolIndex, perform, moveLeft]

theorem scan_nonblank_reaches (a : Symbol) (left right : List Symbol)
    (ha : a ≠ .blank) (hl : ∀ x ∈ left, x ≠ .blank) :
    Reaches scanBack (scanCfg left a right) (scanCfg [] .blank (left.reverse ++ a :: right)) := by
  induction left generalizing a right with
  | nil => simpa using Reaches.step (scan_nonblank_last a right ha) (Reaches.refl _)
  | cons b left ih =>
    have hb : b ≠ .blank := hl b (by simp)
    have ht : ∀ x ∈ left, x ≠ .blank := by intro x hx; exact hl x (by simp [hx])
    have h := Reaches.step (scan_nonblank_next a b left right ha) (ih b (a :: right) hb ht)
    simpa [List.reverse_cons, List.append_assoc] using h

theorem scanBack_reaches (a : Symbol) (left : List Symbol)
    (ha : a ≠ .blank) (hl : ∀ x ∈ left, x ≠ .blank) :
    Reaches scanBack ⟨⟨0, by decide⟩, ⟨a :: left, .blank, []⟩⟩
      ⟨⟨2, by decide⟩, moveRight ⟨[], .blank, left.reverse ++ [a, .blank]⟩⟩ := by
  apply Reaches.step (b := scanCfg left a [.blank])
  · rfl
  · apply reaches_trans (scan_nonblank_reaches a left [.blank] ha hl)
    apply Reaches.step ?_ (.refl _)
    rfl

theorem scanBack_halts (t : Tape) : Halted scanBack ⟨⟨2, by decide⟩, t⟩ := by
  cases t with
  | mk l head r => cases head <;> rfl

#print axioms scanBack_reaches
#print axioms scanBack_halts
end LambdaTuring.Machine
