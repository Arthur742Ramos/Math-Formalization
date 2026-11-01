/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSTotalCompiler
public import LambdaTuring.UniformLambdaEval
public import LambdaTuring.LiftTable
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.Halting

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

/-- Numeral reachability is recursively enumerable. -/
theorem numeralReach_re : REPred NumeralReach := by
  obtain ⟨f, hf, he⟩ := numeralReach_has_partial_observer
  exact hf.dom_re.of_eq he

/-- The universal recursive-code halting relation many-one reduces to numeral reachability. -/
theorem recursiveHalting_manyOne_numeralReach :
    ManyOneReducible (fun p : Nat.Partrec.Code × Nat =>
      (Nat.Partrec.Code.eval p.1 p.2).Dom) NumeralReach :=
  ⟨recursiveHaltingTerm, recursiveHaltingTerm_primrec.to_comp,
    fun p => (recursiveHaltingTerm_correct p).symm⟩

/-- Full-beta Church-numeral reachability is undecidable. -/
theorem numeralReach_undecidable : ¬ ComputablePred NumeralReach := by
  intro h
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_of_manyOneReducible ?_ h
  refine ⟨fun c : Nat.Partrec.Code => recursiveHaltingTerm (c, 0), ?_, ?_⟩
  · exact recursiveHaltingTerm_primrec.to_comp.comp
      (Computable.id.pair (Computable.const 0))
  · intro c
    exact (recursiveHaltingTerm_correct (c, 0)).symm

/-- Absence of a numerical result is not recursively enumerable. -/
theorem numeralReach_complement_not_re : ¬ REPred (fun t => ¬ NumeralReach t) := by
  intro h
  exact numeralReach_undecidable (ComputablePred.computable_iff_re_compl_re'.2 ⟨numeralReach_re, h⟩)

/-- Every r.e. predicate reduces computably to numeral reachability by closed terms. -/
theorem numeralReach_hard {α : Type} [Primcodable α] (p : α → Prop) (hp : REPred p) :
    ∃ f : α → Term, Computable f ∧
      ∀ a, Scoped 0 (f a) ∧ (p a ↔ NumeralReach (f a)) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
  have hdom (a : α) : (Nat.Partrec.Code.eval c (Encodable.encode a)).Dom ↔ p a := by
    rw [hc]
    simp [Encodable.encodek, Part.assert]
  refine ⟨fun a => recursiveHaltingTerm (c, Encodable.encode a), ?_, ?_⟩
  · exact recursiveHaltingTerm_primrec.to_comp.comp
      ((Computable.const c).pair Computable.encode)
  · intro a
    exact ⟨recursiveHaltingTerm_closed _,
      (hdom a).symm.trans (recursiveHaltingTerm_correct (c, Encodable.encode a)).symm⟩

/-- Every r.e. predicate many-one reduces to full-beta numeral reachability. -/
theorem numeralReach_manyOne_complete {α : Type} [Primcodable α] (p : α → Prop)
    (hp : REPred p) : ManyOneReducible p NumeralReach := by
  obtain ⟨f, hf, h⟩ := numeralReach_hard p hp
  exact ⟨f, hf, fun a => (h a).2⟩

/-- No computable Boolean procedure decides numeral reachability even on closed inputs. -/
theorem no_computable_closed_numeral_decider :
    ¬ ∃ d : Term → Bool, Computable d ∧
      ∀ t, Scoped 0 t → (d t = true ↔ NumeralReach t) := by
  rintro ⟨d, hd, hcorrect⟩
  have hp : ComputablePred (fun t : Term => d t = true) := by
    apply Computable.computablePred
    simpa using hd
  have hred : ManyOneReducible
      (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom)
      (fun t : Term => d t = true) := by
    refine ⟨fun c => recursiveHaltingTerm (c, 0), ?_, ?_⟩
    · exact recursiveHaltingTerm_primrec.to_comp.comp
        (Computable.id.pair (Computable.const 0))
    · intro c
      exact (recursiveHaltingTerm_correct (c, 0)).symm.trans
        (hcorrect _ (recursiveHaltingTerm_closed _)).symm
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible hred hp)

#print axioms recursiveHaltingTerm_primrec
#print axioms recursiveHaltingTerm_correct
#print axioms numeralReach_re
#print axioms numeralReach_hard
#print axioms numeralReach_complement_not_re
#print axioms no_computable_closed_numeral_decider

end LambdaTuring
