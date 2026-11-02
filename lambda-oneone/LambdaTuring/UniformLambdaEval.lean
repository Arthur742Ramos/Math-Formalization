/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ExecutableTermCoding
public meta import LambdaTuring.ExecutableTermCoding
public import LambdaTuring.ExtensionalMachine
public meta import LambdaTuring.ExtensionalMachine

@[expose] public section

namespace LambdaTuring

/- The bounded observer is uniform in the lambda syntax as well as the input
and fuel. This supports one evaluator code for all terms, not one choice per
term. It does not itself produce that fixed code as executable syntax. -/
theorem primrec_uniformBreadthObservation :
    Primrec₂ (fun p : Term × Nat => fun k => (breadthObservations k p.1 p.2).head?) := by
  let P := (Term × Nat) × Nat
  have hsteps : Primrec betaSteps := primrec_betaSteps_of_subst primrec_substZero
  have hstart : Primrec (fun p : P => Term.app p.1.1 (church p.1.2)) :=
    primrec_app.comp (Primrec.fst.comp Primrec.fst)
      (primrec_church.comp (Primrec.snd.comp Primrec.fst))
  have hlist : Primrec (fun p : P => breadth p.2 (Term.app p.1.1 (church p.1.2))) :=
    (primrec_breadth_of_steps hsteps).comp hstart Primrec.snd
  have hfilter : Primrec (fun p : P =>
      (breadth p.2 (Term.app p.1.1 (church p.1.2))).filterMap decodeChurch) :=
    Primrec.listFilterMap hlist (primrec_decodeChurch.comp Primrec.snd).to₂
  exact (Primrec.list_head?.comp hfilter).to₂

theorem uniformNumericalValue_partrec :
    Partrec (fun p : Term × Nat => numericalValue p.1 p.2) := by
  have hs : Partrec (fun p : Term × Nat => breadthSearch p.1 p.2) :=
    Partrec.rfindOpt primrec_uniformBreadthObservation.to_comp
  have heq : (fun p : Term × Nat => breadthSearch p.1 p.2) =
      (fun p : Term × Nat => numericalValue p.1 p.2) := by
    funext p
    exact breadthSearch_eq_numericalValue p.1 p.2
  rw [← heq]
  exact hs

def UniformLambdaCode (u : Nat.Partrec.Code) : Prop :=
  ∀ t n, Nat.Partrec.Code.eval u (Nat.pair (executableTermEncode t) n) = numericalValue t n

theorem uniformLambdaCode_exists : ∃ u, UniformLambdaCode u := by
  have hp := uniformNumericalValue_partrec
  change Nat.Partrec (fun n => Part.bind (Part.ofOption (Encodable.decode (α := Term × Nat) n)) fun p =>
    (numericalValue p.1 p.2).map Encodable.encode) at hp
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨u, ?_⟩
  intro t n
  have h := congrFun hu (Encodable.encode (t, n))
  simpa [Encodable.encode_prod_val, executableTermEncode_eq, Part.map_id'] using h

/- This assembler is effective when supplied with an evaluator code. The
existence theorem above does not compute one; a concrete closed evaluator
code and its proof remain a separate obligation. -/
def specializeLambdaCode (u : Nat.Partrec.Code) (t : Term) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry u (executableTermEncode t)

theorem specializeLambdaCode_eval (u : Nat.Partrec.Code) (hu : UniformLambdaCode u)
    (t : Term) (n : Nat) :
    Nat.Partrec.Code.eval (specializeLambdaCode u t) n = numericalValue t n := by
  rw [specializeLambdaCode, Nat.Partrec.Code.eval_curry, hu]

def lambdaToUnaryMachineWith (u : Nat.Partrec.Code) (t : Term) :=
  compiledUnaryMachine (specializeLambdaCode u t)

theorem lambdaToUnaryMachineWith_yields (u : Nat.Partrec.Code) (hu : UniformLambdaCode u)
    (t : Term) (n m : Nat) :
    Machine.Yields (lambdaToUnaryMachineWith u t) n m ↔ NumericalResult t n m := by
  rw [lambdaToUnaryMachineWith, compiledUnaryMachine_yields_iff,
    (compileLambdaTotal_sound (specializeLambdaCode u t)).2 n, specializeLambdaCode_eval u hu,
    mem_numericalValue_iff]

#print axioms primrec_uniformBreadthObservation
#print axioms uniformLambdaCode_exists
#print axioms specializeLambdaCode
#print axioms lambdaToUnaryMachineWith_yields
end LambdaTuring
