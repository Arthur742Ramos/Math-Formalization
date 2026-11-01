/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectCertificateObservation
public meta import LambdaTuring.DirectCertificateObservation
public import LambdaTuring.EncodedMachineEvaluator
public meta import LambdaTuring.EncodedMachineEvaluator

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

def certificateNumericalSearch (t : Term) (n : Nat) : Part Nat :=
  Nat.rfindOpt fun cert => certificateObservation (directTermNumber (.app t (church n))) cert

theorem mem_certificateNumericalSearch_iff (t : Term) (n m : Nat) :
    m ∈ certificateNumericalSearch t n ↔ NumericalResult t n m := by
  constructor
  · intro h
    obtain ⟨cert, hc⟩ := Nat.rfindOpt_spec h
    exact (certificateObservation_iff _ _).1 ⟨cert, hc⟩
  · intro hm
    obtain ⟨cert, hc⟩ := (certificateObservation_iff _ _).2 hm
    have hd : (certificateNumericalSearch t n).Dom := Nat.rfindOpt_dom.2 ⟨cert, m, hc⟩
    obtain ⟨m', hm'⟩ := Part.dom_iff_mem.1 hd
    have hr : NumericalResult t n m' := by
      obtain ⟨cert', hc'⟩ := Nat.rfindOpt_spec hm'
      exact (certificateObservation_iff _ _).1 ⟨cert', hc'⟩
    have heq := numeral_result_unique hr hm
    simpa [heq] using hm'

theorem certificateNumericalSearch_eq (t : Term) (n : Nat) :
    certificateNumericalSearch t n = numericalValue t n := by
  apply Part.ext
  intro m
  rw [mem_certificateNumericalSearch_iff, mem_numericalValue_iff]

def directLambdaTermCode : Code := .comp .left .left
def directLambdaInputCode : Code := .comp .right .left
def directLambdaStartCode : Code := .comp directAppCode
  (.pair directLambdaTermCode (.comp directChurchCode directLambdaInputCode))
def directLambdaObserveCode : Code := .comp certificateObservationCode (.pair directLambdaStartCode .right)
def directLambdaTestCode : Code := .comp zeroTestCode directLambdaObserveCode
def directLambdaSearchCode : Code := .comp (.rfind' directLambdaTestCode) (.pair Code.id .zero)
def directLambdaUnwrapCode : Code := .comp ppredCode directLambdaObserveCode
def directLambdaEvaluatorCode : Code :=
  .comp directLambdaUnwrapCode (.pair Code.id directLambdaSearchCode)

theorem directLambdaObserveCode_eval (t : Term) (n cert : Nat) :
    directLambdaObserveCode.eval (Nat.pair (Nat.pair (directTermNumber t) n) cert) =
      Part.some (Encodable.encode (certificateObservation (directTermNumber (.app t (church n))) cert)) := by
  let input := Nat.pair (Nat.pair (directTermNumber t) n) cert
  have hl : Code.eval .left input = Part.some (Nat.pair (directTermNumber t) n) := by simp [input, Code.eval]
  have ht := evalCompSome .left .left _ _ _ hl
    (show Code.eval .left (Nat.pair (directTermNumber t) n) = Part.some (directTermNumber t) from by simp [Code.eval])
  have hn := evalCompSome .right .left _ _ _ hl
    (show Code.eval .right (Nat.pair (directTermNumber t) n) = Part.some n from by simp [Code.eval])
  have hchurch := evalCompSome directChurchCode directLambdaInputCode _ _ _ hn (directChurchCode_eval n)
  have hp := evalPairSome directLambdaTermCode (.comp directChurchCode directLambdaInputCode) _ _ _ ht hchurch
  have hstart := evalCompSome directAppCode _ _ _ _ hp
    (directTaggedCode_eval 2 (Nat.pair (directTermNumber t) (directTermNumber (church n))))
  have hc : Code.eval .right input = Part.some cert := by simp [input, Code.eval]
  have harg := evalPairSome directLambdaStartCode .right _ _ _ hstart hc
  have h := evalCompSome certificateObservationCode _ _ _ _ harg
    (certificateObservationCode_eval (directTermNumber (.app t (church n))) cert)
  exact h

theorem directLambdaTestCode_eval (t : Term) (n cert : Nat) :
    directLambdaTestCode.eval (Nat.pair (Nat.pair (directTermNumber t) n) cert) =
      Part.some (if (certificateObservation (directTermNumber (.app t (church n))) cert).isSome then 0 else 1) := by
  have h := evalCompSome zeroTestCode directLambdaObserveCode _ _ _ (directLambdaObserveCode_eval t n cert)
    (eval_zeroTestCode (Encodable.encode (certificateObservation (directTermNumber (.app t (church n))) cert)))
  cases he : certificateObservation (directTermNumber (.app t (church n))) cert <;>
    simpa [directLambdaTestCode, he] using h

theorem directLambdaSearchCode_eval (t : Term) (n : Nat) :
    directLambdaSearchCode.eval (Nat.pair (directTermNumber t) n) =
      Nat.rfind (fun cert => (certificateObservation (directTermNumber (.app t (church n))) cert).isSome) := by
  let input := Nat.pair (directTermNumber t) n
  have hpair : Code.eval (.pair Code.id .zero) input = Part.some (Nat.pair input 0) := by
    change Nat.pair <$> Code.eval Code.id input <*> Code.eval .zero input = _
    simp [Code.eval_id, Code.eval, Seq.seq, pure, PFun.pure]
  change (Code.eval (.pair Code.id .zero) input).bind (fun x => Code.eval (.rfind' directLambdaTestCode) x) = _
  rw [hpair, Part.bind_some, Code.eval, Nat.unpaired, Nat.unpair_pair]
  have heval (cert : Nat) : (fun m => decide (m = 0)) <$>
      directLambdaTestCode.eval (Nat.pair input cert) =
        (Part.some ((certificateObservation (directTermNumber (.app t (church n))) cert).isSome) : Part Bool) := by
    rw [directLambdaTestCode_eval]
    cases certificateObservation (directTermNumber (.app t (church n))) cert <;> simp
  simp only [Nat.add_zero]
  rw [show (fun cert => (fun m => decide (m = 0)) <$> directLambdaTestCode.eval (Nat.pair input cert)) =
      (fun cert => (Part.some ((certificateObservation (directTermNumber (.app t (church n))) cert).isSome) : Part Bool)) from funext heval]
  simp [Part.map_id']

theorem directLambdaUnwrapCode_eval (t : Term) (n cert : Nat) :
    directLambdaUnwrapCode.eval (Nat.pair (Nat.pair (directTermNumber t) n) cert) =
      (certificateObservation (directTermNumber (.app t (church n))) cert : Part Nat) := by
  change (directLambdaObserveCode.eval (Nat.pair (Nat.pair (directTermNumber t) n) cert)).bind
    (fun x => ppredCode.eval x) = _
  rw [directLambdaObserveCode_eval, Part.bind_some, eval_ppredCode]
  cases certificateObservation (directTermNumber (.app t (church n))) cert <;> rfl

theorem directLambdaEvaluatorCode_eval (t : Term) (n : Nat) :
    directLambdaEvaluatorCode.eval (Nat.pair (directTermNumber t) n) = numericalValue t n := by
  let input := Nat.pair (directTermNumber t) n
  change (Code.eval (.pair Code.id directLambdaSearchCode) input).bind
    (fun x => directLambdaUnwrapCode.eval x) = _
  change (Nat.pair <$> Code.eval Code.id input <*> directLambdaSearchCode.eval input).bind
    (fun x => directLambdaUnwrapCode.eval x) = _
  rw [Code.eval_id, directLambdaSearchCode_eval, ← certificateNumericalSearch_eq]
  unfold certificateNumericalSearch Nat.rfindOpt
  simp [Seq.seq, input, directLambdaUnwrapCode_eval]

#print axioms directLambdaEvaluatorCode
#print axioms directLambdaEvaluatorCode_eval
end LambdaTuring
