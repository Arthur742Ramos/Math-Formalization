/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSTotalCompiler
public import LambdaTuring.UniformLambdaEval
public import LambdaTuring.LiftTable

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

/-- A term which ignores its input and reduces to the original term. -/
def numeralObserver (t : Term) : Term := .abs (liftFrom 0 t)

theorem numeralObserver_primrec : Primrec numeralObserver := by
  exact primrec_abs.comp (primrec_liftFrom.comp (Primrec.const 0) Primrec.id)

theorem numeralObserver_beta (t : Term) (n : Nat) :
    Reaches (.app (numeralObserver t) (church n)) t := by
  apply Reaches.step (Beta.contract _ _)
  simpa [numeralObserver, substAt_liftFrom] using (Reaches.refl t)

theorem numeralObserver_dom_iff (t : Term) :
    (numericalValue (numeralObserver t) 0).Dom ↔ NumeralReach t := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, reaches_numeral_join (numeralObserver_beta t 0)
      ((mem_numericalValue_iff _ _ _).1 hm)⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, (mem_numericalValue_iff _ _ _).2 ?_⟩
    exact reaches_trans (numeralObserver_beta t 0) hm

/-- A uniform partial-recursive procedure is defined exactly on numeral-reaching terms. -/
theorem numeralReach_has_partial_observer :
    ∃ f : Term →. Nat, Partrec f ∧ ∀ t, (f t).Dom ↔ NumeralReach t := by
  refine ⟨fun t => numericalValue (numeralObserver t) 0, ?_, numeralObserver_dom_iff⟩
  exact uniformNumericalValue_partrec.comp
    (numeralObserver_primrec.to_comp.pair (Computable.const 0))

end LambdaTuring
