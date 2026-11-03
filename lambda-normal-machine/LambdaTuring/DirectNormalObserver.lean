/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.NormalOrder
public meta import LambdaTuring.NormalOrder
public import LambdaTuring.NormalObservation
public meta import LambdaTuring.NormalObservation
public import LambdaTuring.DirectBetaCode
public meta import LambdaTuring.DirectBetaCode
public import LambdaTuring.DirectChurchDecode
public meta import LambdaTuring.DirectChurchDecode
@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

/-- The history key pairs a directly encoded term with zero. The same
representation and root-contraction code as the existing beta-path compiler
are used; zero denotes no reduct and successor encodes a reduct. -/
def normalSelectorReadRep {f : Nat → List Nat → Nat} (child : LiftStepRep f) :=
  LiftStepRep.lookup liftKeyRep (child.pair betaZeroRep)

def normalSelectorLeftRep := normalSelectorReadRep liftLeftChildRep
def normalSelectorRightRep := normalSelectorReadRep liftRightChildRep
def normalSelectorAbsRep := betaWrapAbsRep (normalSelectorReadRep liftPayloadRep)
def normalSelectorAppRep := betaRootRep.select
  (normalSelectorLeftRep.select
    (betaWrapRightRep liftLeftChildRep normalSelectorRightRep)
    (betaWrapLeftRep normalSelectorLeftRep liftRightChildRep))
  betaRootRep
def normalSelectorStepRep := (betaEqualRep liftTagRep betaOneRep).select
  ((betaEqualRep liftTagRep betaTwoRep).select betaZeroRep normalSelectorAppRep)
  normalSelectorAbsRep

def normalSelectorStepCode : Code := normalSelectorStepRep.code

/-- A total numeric formula for one course-of-values selector step, including
fallbacks for numbers that are not valid syntax codes. -/
def normalSelectorStepValue (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let tag := directTag term
  let data := directPayload term
  let read := fun child => (history[key.pred - Nat.pair child 0]?).getD 0
  if tag = 1 then betaWrapAbs (read data)
  else if tag = 2 then
    let root := betaRootValue term
    if root = 0 then
      let left := read data.unpair.1
      if left = 0 then betaWrapRight data.unpair.1 (read data.unpair.2)
      else betaWrapLeft left data.unpair.2
    else root
  else 0

def normalSelectorStepFormula (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let tag := directTag term
  let data := directPayload term
  let read := fun child => (history[key.pred - Nat.pair child 0]?).getD 0
  let root := if (if tag = 2 then 1 else 0) = 0 then 0
    else if (if directTag data.unpair.1 = 1 then 1 else 0) = 0 then 0
    else substValue data.unpair.2 (Nat.pair (directPayload data.unpair.1) 0) + 1
  let wrapAbs := fun r => if r = 0 then 0 else directAbsNumber r.pred + 1
  let wrapLeft := fun r arg => if r = 0 then 0 else directAppNumber r.pred arg + 1
  let wrapRight := fun arg r => if r = 0 then 0 else directAppNumber arg r.pred + 1
  if (if tag = 1 then 1 else 0) = 0 then
    if (if tag = 2 then 1 else 0) = 0 then 0
    else if root = 0 then
      if read data.unpair.1 = 0 then wrapRight data.unpair.1 (read data.unpair.2)
      else wrapLeft (read data.unpair.1) data.unpair.2
    else root
  else wrapAbs (read data)

theorem normalSelectorStepFormula_eq (key : Nat) (history : List Nat) :
    normalSelectorStepFormula key history = normalSelectorStepValue key history := by
  by_cases h1 : directTag key.unpair.1 = 1
  · simp [normalSelectorStepFormula, normalSelectorStepValue, betaWrapAbs, h1]
  · by_cases h2 : directTag key.unpair.1 = 2
    · by_cases hf : directTag (directPayload key.unpair.1).unpair.1 = 1
      · simp [normalSelectorStepFormula, normalSelectorStepValue, betaRootValue, h2, hf]
      · simp [normalSelectorStepFormula, normalSelectorStepValue, betaRootValue,
          betaWrapLeft, betaWrapRight, h2, hf]
    · simp [normalSelectorStepFormula, normalSelectorStepValue, h1, h2]

theorem normalSelectorStepCode_eval (context key : Nat) (history : List Nat) :
    normalSelectorStepCode.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (normalSelectorStepValue key history) := by
  have h := normalSelectorStepRep.sound context key history
  change normalSelectorStepCode.eval _ = Part.some (normalSelectorStepFormula key history) at h
  simpa only [normalSelectorStepFormula_eq] using h

def normalSelectorHistory : Nat → List Nat
  | 0 => []
  | k + 1 => normalSelectorStepValue k (normalSelectorHistory k) :: normalSelectorHistory k

def normalSelectorValue (key : Nat) : Nat :=
  normalSelectorStepValue key (normalSelectorHistory key)

theorem normalSelectorHistory_eq_course (context k : Nat) :
    courseHistory (fun _ n => normalSelectorValue n) context k = normalSelectorHistory k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change normalSelectorValue k :: courseHistory (fun _ n => normalSelectorValue n) context k =
      normalSelectorStepValue k (normalSelectorHistory k) :: normalSelectorHistory k
    rw [ih]
    rfl

def normalSelectorCode : Code := .comp (courseCode normalSelectorStepCode) (.pair .zero Code.id)

theorem normalSelectorCode_any (key : Nat) :
    normalSelectorCode.eval key = Part.some (normalSelectorValue key) := by
  have hstep : ∀ context k,
      normalSelectorStepCode.eval (Nat.pair context
        (Nat.pair k (Encodable.encode (courseHistory (fun _ i => normalSelectorValue i) context k)))) =
          Part.some (normalSelectorValue k) := by
    intro context k
    rw [normalSelectorHistory_eq_course, normalSelectorStepCode_eval]
    rfl
  have hz : Code.eval .zero key = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id key 0 key hz (Code.eval_id key)
  have hcourse := courseCode_eval normalSelectorStepCode (fun _ k => normalSelectorValue k) hstep 0 key
  exact evalCompSome (courseCode normalSelectorStepCode) (.pair .zero Code.id) _ _ _ hp hcourse

theorem normalSelectorRead_correct (key child : Nat) (hlt : Nat.pair child 0 < key) :
    (normalSelectorHistory key)[key.pred - Nat.pair child 0]?.getD 0 =
      normalSelectorValue (Nat.pair child 0) := by
  have hread := courseHistory_lookup (fun _ n => normalSelectorValue n) 0 key (Nat.pair child 0) hlt
  rw [normalSelectorHistory_eq_course] at hread
  simp only [Nat.pred_eq_sub_one, hread, Option.getD_some]

theorem normalOrderStep_app_nonabs (f x : Term) (hn : ¬ ∃ b, f = .abs b) :
    normalOrderStep (.app f x) =
      match normalOrderStep f with
      | some u => some (.app u x)
      | Option.none => (normalOrderStep x).map (Term.app f) := by
  cases hf : normalOrderStep f with
  | some u => simpa [hf] using normalOrderStep_app_left hn hf
  | none =>
    cases hx : normalOrderStep x with
    | some u => simpa [hf, hx] using normalOrderStep_app_right hn hf hx
    | none =>
      simp only [Option.map_none]
      apply (normalOrderStep_none_iff _).2
      rintro ⟨_, h⟩
      cases h with
      | contract body value => exact hn ⟨body, rfl⟩
      | appLeft h => exact ((normalOrderStep_none_iff _).1 hf) ⟨_, h⟩
      | appRight h => exact ((normalOrderStep_none_iff _).1 hx) ⟨_, h⟩

/-- On valid term encodings the explicit course computation selects exactly
the deterministic full-beta normal-order successor, if any. -/
theorem normalSelectorValue_correct (t : Term) :
    normalSelectorValue (Nat.pair (directTermNumber t) 0) =
      Encodable.encode ((normalOrderStep t).map directTermNumber) := by
  induction t with
  | var i =>
    simp [normalSelectorValue, normalSelectorStepValue, directTag,
      directTermNumber, normalOrderStep_var]
  | abs body ih =>
    have hlt := Nat.pair_lt_pair_left 0 (directTermNumber_abs_lt body)
    have hread := normalSelectorRead_correct (Nat.pair (directTermNumber (.abs body)) 0)
      (directTermNumber body) hlt
    simp only [directTermNumber, Nat.succ_eq_add_one, Nat.pred_eq_sub_one] at hread
    rw [normalOrderStep_abs]
    unfold normalSelectorValue
    cases hs : normalOrderStep body <;>
      simp [normalSelectorStepValue, directTag, directPayload, directTermNumber,
        betaWrapAbs, directAbsNumber, hread, ih, hs]
  | app f x ihf ihx =>
    have hlf := Nat.pair_lt_pair_left 0 (directTermNumber_app_left_lt f x)
    have hlx := Nat.pair_lt_pair_left 0 (directTermNumber_app_right_lt f x)
    have hreadf := normalSelectorRead_correct (Nat.pair (directTermNumber (.app f x)) 0)
      (directTermNumber f) hlf
    have hreadx := normalSelectorRead_correct (Nat.pair (directTermNumber (.app f x)) 0)
      (directTermNumber x) hlx
    simp only [directTermNumber, Nat.succ_eq_add_one, Nat.pred_eq_sub_one] at hreadf hreadx
    by_cases habs : ∃ b, f = .abs b
    · obtain ⟨b, rfl⟩ := habs
      rw [normalOrderStep_root]
      simp [normalSelectorValue, normalSelectorStepValue, directTag, directPayload,
        directTermNumber, betaRootValue, substValue_correct]
    · have hroot : betaRootValue (directTermNumber (.app f x)) = 0 := by
        cases f with
        | var i => simp [betaRootValue, directTag, directPayload, directTermNumber]
        | abs b => exact False.elim (habs ⟨b, rfl⟩)
        | app a b => simp [betaRootValue, directTag, directPayload, directTermNumber]
      rw [normalOrderStep_app_nonabs f x habs]
      unfold normalSelectorValue
      cases hf : normalOrderStep f <;> cases hx : normalOrderStep x <;>
        simp [normalSelectorStepValue, directTag, directPayload, directTermNumber,
          betaWrapLeft, betaWrapRight, directAppNumber, hreadf, hreadx, ihf, ihx, hf, hx,
          betaRootValue] at *
      all_goals simp_all

theorem normalSelectorCode_correct (t : Term) :
    normalSelectorCode.eval (Nat.pair (directTermNumber t) 0) =
      Part.some (Encodable.encode ((normalOrderStep t).map directTermNumber)) := by
  rw [normalSelectorCode_any, normalSelectorValue_correct]

/-- Package the course selector as a unary code taking the direct term number. -/
def directNormalStepCode : Code := .comp normalSelectorCode (.pair Code.id .zero)

theorem directNormalStepCode_eval (t : Term) :
    directNormalStepCode.eval (directTermNumber t) =
      Part.some (Encodable.encode ((normalOrderStep t).map directTermNumber)) := by
  let input := directTermNumber t
  have hp := evalPairSome Code.id .zero input input 0 (Code.eval_id input) rfl
  exact evalCompSome normalSelectorCode (.pair Code.id .zero) _ _ _ hp
    (normalSelectorCode_correct t)

theorem directNormalStepCode_normal {t : Term} (h : normalOrderStep t = Option.none) :
    directNormalStepCode.eval (directTermNumber t) = Part.some 0 := by
  simpa [h] using directNormalStepCode_eval t

theorem directNormalStepCode_step {t u : Term} (h : normalOrderStep t = some u) :
    directNormalStepCode.eval (directTermNumber t) = Part.some (directTermNumber u + 1) := by
  simpa [h] using directNormalStepCode_eval t

theorem directNormalStepCode_any (term : Nat) :
    directNormalStepCode.eval term = Part.some (normalSelectorValue (Nat.pair term 0)) := by
  have hp := evalPairSome Code.id .zero term term 0 (Code.eval_id term) rfl
  exact evalCompSome normalSelectorCode (.pair Code.id .zero) _ _ _ hp
    (normalSelectorCode_any (Nat.pair term 0))

def directNormalTickValue (term : Nat) : Nat :=
  let next := normalSelectorValue (Nat.pair term 0)
  if next = 0 then term else next.pred

def directNormalTickCode : Code :=
  chooseZeroCode directNormalStepCode Code.id (.comp predCode directNormalStepCode)

theorem directNormalTickCode_eval (term : Nat) :
    directNormalTickCode.eval term = Part.some (directNormalTickValue term) := by
  let next := normalSelectorValue (Nat.pair term 0)
  have hn := directNormalStepCode_any term
  have hp := evalCompSome predCode directNormalStepCode _ _ _ hn (eval_predCode next)
  have h := chooseZeroCode_eval directNormalStepCode Code.id (.comp predCode directNormalStepCode)
    _ _ _ _ hn (Code.eval_id term) hp
  simpa [directNormalTickCode, directNormalTickValue, next] using h

theorem directNormalTickValue_correct (t : Term) :
    directNormalTickValue (directTermNumber t) =
      directTermNumber ((normalOrderStep t).getD t) := by
  have h := normalSelectorValue_correct t
  cases hs : normalOrderStep t with
  | none => simp [directNormalTickValue, hs] at h ⊢; simp [h]
  | some u => simp [directNormalTickValue, hs] at h ⊢; simp [h]

def directNormalIterValue : Nat → Nat → Nat
  | 0, term => term
  | fuel + 1, term => directNormalIterValue fuel (directNormalTickValue term)

theorem directNormalIterValue_comm (fuel term : Nat) :
    directNormalTickValue (directNormalIterValue fuel term) =
      directNormalIterValue fuel (directNormalTickValue term) := by
  induction fuel generalizing term with
  | zero => rfl
  | succ fuel ih => simpa [directNormalIterValue] using ih (directNormalTickValue term)

def directNormalIterCode : Code := .prec Code.id (.comp directNormalTickCode (.comp .right .right))

theorem directNormalIterCode_eval (term fuel : Nat) :
    directNormalIterCode.eval (Nat.pair term fuel) = Part.some (directNormalIterValue fuel term) := by
  induction fuel with
  | zero =>
    rw [directNormalIterCode, Code.eval_prec_zero]
    exact Code.eval_id term
  | succ fuel ih =>
    rw [directNormalIterCode, Code.eval_prec_succ]
    change (directNormalIterCode.eval (Nat.pair term fuel)).bind _ = _
    rw [ih, Part.bind_some]
    have hp : Code.eval (.comp .right .right) (Nat.pair term (Nat.pair fuel (directNormalIterValue fuel term))) =
        Part.some (directNormalIterValue fuel term) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have hs := evalCompSome directNormalTickCode (.comp .right .right) _ _ _ hp
      (directNormalTickCode_eval (directNormalIterValue fuel term))
    rw [directNormalIterValue_comm] at hs
    exact hs

theorem directNormalIterValue_correct (fuel : Nat) (t : Term) :
    directNormalIterValue fuel (directTermNumber t) = directTermNumber (normalOrderRun fuel t) := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    rw [directNormalIterValue, directNormalTickValue_correct]
    cases hs : normalOrderStep t with
    | none =>
      have h := ih t
      rw [normalOrderRun_fixed hs fuel] at h
      simpa [normalOrderRun, hs] using h
    | some u => simpa [normalOrderRun, hs] using ih u

theorem directNormalIterCode_correct (fuel : Nat) (t : Term) :
    directNormalIterCode.eval (Nat.pair (directTermNumber t) fuel) =
      Part.some (directTermNumber (normalOrderRun fuel t)) := by
  rw [directNormalIterCode_eval, directNormalIterValue_correct]

/-- Encoded nested option: zero means continue, one means a nonnumerical
normal form, and `n + 2` means Church numeral `n`. -/
def directNormalStageAtValue (term : Nat) : Nat :=
  if normalSelectorValue (Nat.pair term 0) = 0 then
    Encodable.encode (directChurchSearch term (term + 1)) + 1
  else 0

def directNormalStageAtCode : Code :=
  chooseZeroCode directNormalStepCode (.comp .succ directChurchDecodeCode) .zero

theorem directNormalStageAtCode_eval (term : Nat) :
    directNormalStageAtCode.eval term = Part.some (directNormalStageAtValue term) := by
  let result := directChurchSearch term (term + 1)
  have hs := directNormalStepCode_any term
  have hd := directChurchDecodeCode_eval term
  have hy := evalCompSome .succ directChurchDecodeCode _ _ _ hd
    (show Code.eval .succ (Encodable.encode result) = Part.some (Encodable.encode result + 1) from rfl)
  have hz : Code.eval .zero term = Part.some 0 := rfl
  have h := chooseZeroCode_eval directNormalStepCode (.comp .succ directChurchDecodeCode) .zero
    _ _ _ _ hs hy hz
  simpa [directNormalStageAtCode, directNormalStageAtValue, result] using h

theorem directNormalStageAtCode_correct (t : Term) :
    directNormalStageAtCode.eval (directTermNumber t) =
      Part.some (Encodable.encode (match normalOrderStep t with
        | Option.none => some (normalDecode t)
        | some _ => none)) := by
  rw [directNormalStageAtCode_eval, directNormalStageAtValue,
    normalSelectorValue_correct, directChurchSearch_eq_decodeChurch, ← normalDecode_eq_decodeChurch]
  cases hs : normalOrderStep t <;> simp

def directNormalStageCode : Code := .comp directNormalStageAtCode directNormalIterCode

theorem directNormalStageCode_correct (t : Term) (fuel : Nat) :
    directNormalStageCode.eval (Nat.pair (directTermNumber t) fuel) =
      Part.some (Encodable.encode (normalObservationStage t fuel)) := by
  have hi := directNormalIterCode_correct fuel t
  have hstage := directNormalStageAtCode_correct (normalOrderRun fuel t)
  have h := evalCompSome directNormalStageAtCode directNormalIterCode _ _ _ hi hstage
  cases hs : normalOrderStep (normalOrderRun fuel t) <;>
    simpa [directNormalStageCode, normalObservationStage, hs] using h

def directNormalTestCode : Code := .comp zeroTestCode directNormalStageCode
def directNormalSearchCode : Code := .comp (.rfind' directNormalTestCode) (.pair Code.id .zero)
def directNormalUnwrapCode : Code := .comp ppredCode directNormalStageCode
def directNormalObserverCode : Code :=
  .comp directNormalUnwrapCode (.pair Code.id directNormalSearchCode)

theorem directNormalTestCode_eval (t : Term) (fuel : Nat) :
    directNormalTestCode.eval (Nat.pair (directTermNumber t) fuel) =
      Part.some (if (normalObservationStage t fuel).isSome then 0 else 1) := by
  have h := evalCompSome zeroTestCode directNormalStageCode _ _ _ (directNormalStageCode_correct t fuel)
    (eval_zeroTestCode (Encodable.encode (normalObservationStage t fuel)))
  cases hs : normalObservationStage t fuel <;> simpa [directNormalTestCode, hs] using h

theorem directNormalSearchCode_eval (t : Term) :
    directNormalSearchCode.eval (directTermNumber t) =
      Nat.rfind (fun fuel => (normalObservationStage t fuel).isSome) := by
  let input := directTermNumber t
  have hpair : Code.eval (.pair Code.id .zero) input = Part.some (Nat.pair input 0) := by
    change Nat.pair <$> Code.eval Code.id input <*> Code.eval .zero input = _
    simp [Code.eval_id, Code.eval, Seq.seq, pure, PFun.pure]
  change (Code.eval (.pair Code.id .zero) input).bind (fun x => Code.eval (.rfind' directNormalTestCode) x) = _
  rw [hpair, Part.bind_some, Code.eval, Nat.unpaired, Nat.unpair_pair]
  have heval (fuel : Nat) : (fun m => decide (m = 0)) <$>
      directNormalTestCode.eval (Nat.pair input fuel) =
        (Part.some ((normalObservationStage t fuel).isSome) : Part Bool) := by
    rw [directNormalTestCode_eval]
    cases normalObservationStage t fuel <;> simp
  simp only [Nat.add_zero]
  rw [show (fun fuel => (fun m => decide (m = 0)) <$> directNormalTestCode.eval (Nat.pair input fuel)) =
      (fun fuel => (Part.some ((normalObservationStage t fuel).isSome) : Part Bool)) from funext heval]
  simp [Part.map_id']

theorem directNormalUnwrapCode_eval (t : Term) (fuel : Nat) :
    directNormalUnwrapCode.eval (Nat.pair (directTermNumber t) fuel) =
      ((normalObservationStage t fuel).map Encodable.encode : Option Nat) := by
  change (directNormalStageCode.eval (Nat.pair (directTermNumber t) fuel)).bind
    (fun x => ppredCode.eval x) = _
  rw [directNormalStageCode_correct, Part.bind_some, eval_ppredCode]
  cases normalObservationStage t fuel <;> simp

theorem directNormalObserverCode_eval (t : Term) :
    directNormalObserverCode.eval (directTermNumber t) =
      (normalObservation t).map Encodable.encode := by
  let input := directTermNumber t
  change (Code.eval (.pair Code.id directNormalSearchCode) input).bind
    (fun x => directNormalUnwrapCode.eval x) = _
  change (Nat.pair <$> Code.eval Code.id input <*> directNormalSearchCode.eval input).bind
    (fun x => directNormalUnwrapCode.eval x) = _
  rw [Code.eval_id, directNormalSearchCode_eval]
  unfold normalObservation Nat.rfindOpt
  simp [Seq.seq, input, directNormalUnwrapCode_eval]
  congr 1
  funext fuel
  cases normalObservationStage t fuel <;> simp


#print axioms directNormalObserverCode
#print axioms directNormalObserverCode_eval
end LambdaTuring
