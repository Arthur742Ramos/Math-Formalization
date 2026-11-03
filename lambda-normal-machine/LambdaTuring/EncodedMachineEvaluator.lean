/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedObservation
public meta import LambdaTuring.EncodedObservation
public import LambdaTuring.ExecutableRawTableEncoding
public meta import LambdaTuring.ExecutableRawTableEncoding

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def observeTestCode : Code := .comp zeroTestCode observeCode
def observeSearchCode : Code := .comp (.rfind' observeTestCode) (.pair Code.id .zero)
def observeUnwrapCode : Code := .comp ppredCode observeCode
def uniformMachineEvaluatorCode : Code :=
  .comp observeUnwrapCode (.pair Code.id observeSearchCode)

theorem observeTestCode_eval (p : RawTable) (n fuel : Nat) :
    observeTestCode.eval (Nat.pair (Nat.pair (Encodable.encode p) n) fuel) =
      Part.some (if (rawObserveExact p n fuel).isSome then 0 else 1) := by
  have h := evalCompSome zeroTestCode observeCode _ _ _ (observeCode_eval p n fuel)
    (eval_zeroTestCode (Encodable.encode (rawObserveExact p n fuel)))
  cases he : rawObserveExact p n fuel <;> simpa [observeTestCode, he] using h

theorem observeSearchCode_eval (p : RawTable) (n : Nat) :
    observeSearchCode.eval (Nat.pair (Encodable.encode p) n) =
      Nat.rfind (fun fuel => (rawObserveExact p n fuel).isSome) := by
  let input := Nat.pair (Encodable.encode p) n
  have hpair : Code.eval (.pair Code.id .zero) input = Part.some (Nat.pair input 0) := by
    change Nat.pair <$> Code.eval Code.id input <*> Code.eval .zero input = _
    simp [Code.eval_id, Code.eval, Seq.seq, pure, PFun.pure]
  change (Code.eval (.pair Code.id .zero) input).bind (fun x => Code.eval (.rfind' observeTestCode) x) = _
  rw [hpair, Part.bind_some, Code.eval, Nat.unpaired, Nat.unpair_pair]
  have heval (fuel : Nat) : (fun m => decide (m = 0)) <$>
      observeTestCode.eval (Nat.pair input fuel) =
        (Part.some ((rawObserveExact p n fuel).isSome) : Part Bool) := by
    rw [observeTestCode_eval]
    cases rawObserveExact p n fuel <;> simp
  simp only [Nat.add_zero]
  rw [show (fun fuel => (fun m => decide (m = 0)) <$> observeTestCode.eval (Nat.pair input fuel)) =
      (fun fuel => (Part.some ((rawObserveExact p n fuel).isSome) : Part Bool)) from funext heval]
  simp [Part.map_id']

theorem observeUnwrapCode_eval (p : RawTable) (n fuel : Nat) :
    observeUnwrapCode.eval (Nat.pair (Nat.pair (Encodable.encode p) n) fuel) =
      (rawObserveExact p n fuel : Part Nat) := by
  change (observeCode.eval (Nat.pair (Nat.pair (Encodable.encode p) n) fuel)).bind
    (fun x => ppredCode.eval x) = _
  rw [observeCode_eval, Part.bind_some, eval_ppredCode]
  cases rawObserveExact p n fuel <;> rfl

theorem uniformMachineEvaluatorCode_eval (p : RawTable) (n : Nat) :
    uniformMachineEvaluatorCode.eval (Nat.pair (Encodable.encode p) n) = rawValue p n := by
  let input := Nat.pair (Encodable.encode p) n
  change (Code.eval (.pair Code.id observeSearchCode) input).bind
    (fun x => observeUnwrapCode.eval x) = _
  change (Nat.pair <$> Code.eval Code.id input <*> observeSearchCode.eval input).bind
    (fun x => observeUnwrapCode.eval x) = _
  rw [Code.eval_id, observeSearchCode_eval]
  unfold rawValue Nat.rfindOpt
  simp [Seq.seq, input, observeUnwrapCode_eval]

theorem uniformMachineEvaluatorCode_correct : UniformMachineCode uniformMachineEvaluatorCode :=
  uniformMachineEvaluatorCode_eval

/-- Effective compilation of any public finite machine to a closed lambda term. -/
def machineToLambda {states : Nat} (p : Program states) : Term :=
  compileLambdaTotal (Code.curry uniformMachineEvaluatorCode (rawTableNumber (eraseProgram p)))

theorem machineToLambda_eq_with {states : Nat} (p : Program states) :
    machineToLambda p = machineToLambdaWith uniformMachineEvaluatorCode p := by
  simp [machineToLambda, machineToLambdaWith, specializeMachineCode, rawTableNumber_eq]

theorem machineToLambda_correct {states : Nat} (p : Program states) :
    Scoped 0 (machineToLambda p) ∧ ∀ n m,
      NumericalResult (machineToLambda p) n m ↔ Yields p n m :=
  (machineToLambda_eq_with p).symm ▸
    machineToLambdaWith_correct uniformMachineEvaluatorCode uniformMachineEvaluatorCode_correct p

theorem machineToLambda_no_result {states : Nat} (p : Program states) (n : Nat) :
    (∀ m, ¬ NumericalResult (machineToLambda p) n m) ↔ (∀ m, ¬ Yields p n m) := by
  simp only [(machineToLambda_correct p).2 n]

#print axioms uniformMachineEvaluatorCode
#print axioms uniformMachineEvaluatorCode_eval
#print axioms machineToLambda
#print axioms machineToLambda_correct
end LambdaTuring.Machine
