/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectEqualityCode
public meta import LambdaTuring.DirectEqualityCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine

def directChurchSearch (target : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => if target = directTermNumber (church k) then some k else directChurchSearch target k

def churchSearchTargetCode : Code := .left
def churchSearchIndexCode : Code := .comp .left .right
def churchSearchPriorCode : Code := .comp .right .right
def churchSearchCandidateCode : Code := .comp directChurchCode churchSearchIndexCode
def churchSearchEqualCode : Code := .comp equalNatCode (.pair churchSearchTargetCode churchSearchCandidateCode)
def churchSearchSomeCode : Code := .comp .succ churchSearchIndexCode
def churchSearchStepCode : Code := chooseZeroCode churchSearchEqualCode churchSearchPriorCode churchSearchSomeCode
def churchSearchCode : Code := .prec .zero churchSearchStepCode
def directChurchDecodeCode : Code := .comp churchSearchCode (.pair Code.id (.comp .succ Code.id))

theorem churchSearchStepCode_eval (target k : Nat) (prior : Option Nat) :
    churchSearchStepCode.eval (Nat.pair target (Nat.pair k (Encodable.encode prior))) =
      Part.some (Encodable.encode (if target = directTermNumber (church k) then some k else prior)) := by
  let input := Nat.pair target (Nat.pair k (Encodable.encode prior))
  have ht : churchSearchTargetCode.eval input = Part.some target := by simp [input, churchSearchTargetCode, Code.eval]
  have hr : Code.eval .right input = Part.some (Nat.pair k (Encodable.encode prior)) := by simp [input, Code.eval]
  have hk' : Code.eval .left (Nat.pair k (Encodable.encode prior)) = Part.some k := by simp [Code.eval]
  have hp' : Code.eval .right (Nat.pair k (Encodable.encode prior)) = Part.some (Encodable.encode prior) := by simp [Code.eval]
  have hk := evalCompSome .left .right _ _ _ hr hk'
  have hp := evalCompSome .right .right _ _ _ hr hp'
  have hc := evalCompSome directChurchCode churchSearchIndexCode _ _ _ hk (directChurchCode_eval k)
  have heqInput := evalPairSome churchSearchTargetCode churchSearchCandidateCode _ _ _ ht hc
  have heq := evalCompSome equalNatCode _ _ _ _ heqInput (equalNatCode_eval target (directTermNumber (church k)))
  have hsome := evalCompSome .succ churchSearchIndexCode _ _ _ hk
    (show Code.eval .succ k = Part.some (Nat.succ k) from rfl)
  have h := chooseZeroCode_eval churchSearchEqualCode churchSearchPriorCode churchSearchSomeCode _ _ _ _ heq hp hsome
  by_cases he : target = directTermNumber (church k)
  · simpa [churchSearchStepCode, input, he] using h
  · simpa [churchSearchStepCode, input, he] using h

theorem churchSearchCode_eval (target bound : Nat) :
    churchSearchCode.eval (Nat.pair target bound) = Part.some (Encodable.encode (directChurchSearch target bound)) := by
  induction bound with
  | zero => rw [churchSearchCode, Code.eval_prec_zero]; rfl
  | succ n ih =>
    rw [churchSearchCode, Code.eval_prec_succ]
    change (churchSearchCode.eval (Nat.pair target n)).bind _ = _
    rw [ih]
    change (Part.some (Encodable.encode (directChurchSearch target n))).bind
      (fun z => churchSearchStepCode.eval (Nat.pair target (Nat.pair n z))) = _
    rw [Part.bind_some, churchSearchStepCode_eval]
    rfl

theorem directChurchDecodeCode_eval (target : Nat) :
    directChurchDecodeCode.eval target = Part.some (Encodable.encode (directChurchSearch target (target + 1))) := by
  have hs : Code.eval (.comp .succ Code.id) target = Part.some (target + 1) := by
    exact evalCompSome .succ Code.id _ _ _ (Code.eval_id target) (show Code.eval .succ target = _ from rfl)
  have hp := evalPairSome Code.id (.comp .succ Code.id) _ _ _ (Code.eval_id target) hs
  exact evalCompSome churchSearchCode _ _ _ _ hp (churchSearchCode_eval target (target + 1))

theorem directChurchSearch_some_iff (target bound n : Nat) :
    directChurchSearch target bound = some n ↔
      n < bound ∧ directTermNumber (church n) = target := by
  induction bound with
  | zero => simp [directChurchSearch]
  | succ bound ih =>
    simp only [directChurchSearch]
    by_cases he : target = directTermNumber (church bound)
    · simp only [he, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hn
        subst n
        exact ⟨by omega, rfl⟩
      · rintro ⟨_, hn⟩
        apply church_injective
        apply directTermNumber_injective
        exact hn.symm
    · simp only [he, ↓reduceIte, ih]
      constructor
      · rintro ⟨hn, hncode⟩
        exact ⟨by omega, hncode⟩
      · rintro ⟨hn, hncode⟩
        have hne : n ≠ bound := by
          intro h
          subst n
          exact he hncode.symm
        exact ⟨by omega, hncode⟩

theorem directChurchBody_bound (n : Nat) : n ≤ directTermNumber (churchBody n) := by
  induction n with
  | zero => simp [churchBody, directTermNumber]
  | succ n ih =>
    have h := directTermNumber_app_right_lt (.var 1) (churchBody n)
    change directTermNumber (churchBody n) < directTermNumber (churchBody (n + 1)) at h
    omega

theorem directChurch_bound (n : Nat) : n ≤ directTermNumber (church n) := by
  have h₁ := directChurchBody_bound n
  have h₂ := directTermNumber_abs_lt (churchBody n)
  have h₃ := directTermNumber_abs_lt (.abs (churchBody n))
  change directTermNumber (.abs (churchBody n)) < directTermNumber (church n) at h₃
  omega

theorem directChurchSearch_eq_decodeChurch (t : Term) :
    directChurchSearch (directTermNumber t) (directTermNumber t + 1) = decodeChurch t := by
  cases hs : directChurchSearch (directTermNumber t) (directTermNumber t + 1) with
  | none =>
    cases hd : decodeChurch t with
    | none => rfl
    | some n =>
      have ht : t = church n := (decodeChurch_iff t n).1 hd
      have hb : n < directTermNumber t + 1 := by
        rw [ht]
        have := directChurch_bound n
        omega
      have hn := (directChurchSearch_some_iff (directTermNumber t) (directTermNumber t + 1) n).2
        ⟨hb, (congrArg directTermNumber ht).symm⟩
      rw [hs] at hn
      contradiction
  | some n =>
    have hn := (directChurchSearch_some_iff (directTermNumber t) (directTermNumber t + 1) n).1 hs
    have ht : t = church n := directTermNumber_injective hn.2.symm
    rw [(decodeChurch_iff t n).2 ht]

theorem directChurchDecodeCode_correct (t : Term) :
    directChurchDecodeCode.eval (directTermNumber t) = Part.some (Encodable.encode (decodeChurch t)) := by
  rw [directChurchDecodeCode_eval, directChurchSearch_eq_decodeChurch]

theorem directChurchDecodeCode_numeral_iff (t : Term) (n : Nat) :
    directChurchDecodeCode.eval (directTermNumber t) = Part.some (Encodable.encode (some n)) ↔
      t = church n := by
  rw [directChurchDecodeCode_correct]
  constructor
  · intro h
    exact (decodeChurch_iff t n).1 (Encodable.encode_injective (Part.some_injective h))
  · intro h
    rw [(decodeChurch_iff t n).2 h]

theorem directChurchDecodeCode_none_iff (t : Term) :
    directChurchDecodeCode.eval (directTermNumber t) = Part.some 0 ↔ ∀ n, t ≠ church n := by
  rw [directChurchDecodeCode_correct]
  constructor
  · intro h n hn
    rw [(decodeChurch_iff t n).2 hn] at h
    simp at h
  · intro hn
    have hnone : decodeChurch t = Option.none := by
      cases hd : decodeChurch t with
      | none => rfl
      | some n => exact False.elim (hn n ((decodeChurch_iff t n).1 hd))
    rw [hnone]
    rfl

#print axioms directChurchDecodeCode
#print axioms directChurchDecodeCode_eval
#print axioms directChurchDecodeCode_correct
#print axioms directChurchDecodeCode_none_iff
end LambdaTuring
