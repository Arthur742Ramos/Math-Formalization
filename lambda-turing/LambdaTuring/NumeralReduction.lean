/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSTotalCompiler

@[expose] public section

namespace LambdaTuring

/-- Full-beta reachability of some Church numeral from the given syntax. -/
def NumeralReach (t : Term) : Prop := ∃ m, Reaches t (church m)

/-- Encode a recursive-code/input halting question as a closed lambda term. -/
def recursiveHaltingTerm (p : Nat.Partrec.Code × Nat) : Term :=
  .app (compileLambdaTotal (.comp p.1 (.const p.2))) (church 0)

theorem recursiveHaltingTerm_closed (p : Nat.Partrec.Code × Nat) :
    Scoped 0 (recursiveHaltingTerm p) := by
  change Scoped 0 (compileLambdaTotal (.comp p.1 (.const p.2))) ∧ Scoped 0 (church 0)
  exact ⟨(compileLambdaTotal_sound _).1, church_closed 0⟩

theorem recursiveHaltingTerm_primrec : Primrec recursiveHaltingTerm := by
  have hcode : Primrec (fun p : Nat.Partrec.Code × Nat =>
      Nat.Partrec.Code.comp p.1 (.const p.2)) :=
    Nat.Partrec.Code.primrec₂_comp.comp Primrec.fst
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd)
  exact primrec_app.comp (primrec_compileLambdaTotal.comp hcode) (Primrec.const _)

theorem recursiveHaltingTerm_correct (p : Nat.Partrec.Code × Nat) :
    NumeralReach (recursiveHaltingTerm p) ↔ (Nat.Partrec.Code.eval p.1 p.2).Dom := by
  have heval : Nat.Partrec.Code.eval (.comp p.1 (.const p.2)) 0 =
      Nat.Partrec.Code.eval p.1 p.2 := by
    change (Nat.Partrec.Code.eval (.const p.2) 0).bind (fun n => Nat.Partrec.Code.eval p.1 n) = _
    rw [Nat.Partrec.Code.eval_const, Part.bind_some]
  have hs := (compileLambdaTotal_sound (.comp p.1 (.const p.2))).2 0
  change (∃ m, NumericalResult (compileLambdaTotal (.comp p.1 (.const p.2))) 0 m) ↔ _
  rw [← heval, ← hs, Part.dom_iff_mem]
  exact exists_congr fun m => (mem_numericalValue_iff _ _ _).symm

end LambdaTuring
