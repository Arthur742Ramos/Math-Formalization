/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The theorem holes are standalone comparison obligations. This module is not
imported by the solution. The model and syntax encoding are fixed definitions.
-/
module
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Data.PFun

@[expose] public section
namespace LambdaTuring
open Nat.Partrec

/-- Untyped lambda terms with de Bruijn indices. -/
inductive Term where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Lift indices free at or above a cutoff. -/
def liftFrom (cutoff : Nat) : Term → Term
  | .var i => .var (if i < cutoff then i else i + 1)
  | .abs body => .abs (liftFrom (cutoff + 1) body)
  | .app f x => .app (liftFrom cutoff f) (liftFrom cutoff x)

def liftBy : Nat → Term → Term
  | 0, t => t
  | n + 1, t => liftFrom 0 (liftBy n t)

/-- Capture-avoiding substitution and removal of the discharged binder. -/
def substAt (depth : Nat) (value : Term) : Term → Term
  | .var i => if i = depth then liftBy depth value
      else .var (if depth < i then i - 1 else i)
  | .abs body => .abs (substAt (depth + 1) value body)
  | .app f x => .app (substAt depth value f) (substAt depth value x)

/-- Full compatible beta reduction, including both application branches and binders. -/
inductive Beta : Term → Term → Prop where
  | contract (body value : Term) : Beta (.app (.abs body) value) (substAt 0 value body)
  | abs {a b : Term} : Beta a b → Beta (.abs a) (.abs b)
  | appLeft {a b x : Term} : Beta a b → Beta (.app a x) (.app b x)
  | appRight {f a b : Term} : Beta a b → Beta (.app f a) (.app f b)

/-- Reflexive-transitive full-beta reachability. -/
inductive Reaches : Term → Term → Prop where
  | refl (t : Term) : Reaches t t
  | step {a b c : Term} : Beta a b → Reaches b c → Reaches a c

def churchBody : Nat → Term
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchBody n)

/-- Church numeral using variables 1 and 0 for the function and argument. -/
def church (n : Nat) : Term := .abs (.abs (churchBody n))

/-- All free indices lie below the supplied binder depth. -/
def Scoped (depth : Nat) : Term → Prop
  | .var i => i < depth
  | .abs body => Scoped (depth + 1) body
  | .app f x => Scoped depth f ∧ Scoped depth x

/-- A numerical observation is reachability of the corresponding Church numeral. -/
def NumericalResult (t : Term) (n m : Nat) : Prop :=
  Reaches (.app t (church n)) (church m)

/-- Exact partial numerical observation; its domain is existence of a numeral. -/
noncomputable def numericalValue (t : Term) (n : Nat) : Part Nat :=
  ⟨∃ m, NumericalResult t n m, fun h => Classical.choose h⟩

/-- A closed term represents a partial numerical function exactly. -/
def Represents (t : Term) (f : Nat →. Nat) : Prop :=
  Scoped 0 t ∧ ∀ n, numericalValue t n = f n

def LambdaComputable (f : Nat →. Nat) : Prop := ∃ t, Represents t f


def encodeTerm : Term → Code
  | .app a b => .pair (encodeTerm a) (encodeTerm b)
  | .abs t => .rfind' (encodeTerm t)
  | .var n => .prec .zero (Code.const n)

def decodeConst : Code → Option Nat
  | .zero => some 0
  | .comp .succ c => (decodeConst c).map Nat.succ
  | _ => none

def decodeTerm : Code → Option Term
  | .prec .zero c => (decodeConst c).map Term.var
  | .rfind' c => (decodeTerm c).map Term.abs
  | .pair a b => do
      let a' ← decodeTerm a
      let b' ← decodeTerm b
      pure (.app a' b')
  | _ => none

theorem decodeConst_const (n : Nat) : decodeConst (Code.const n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Code.const, decodeConst, ih]


theorem decodeConst_sound (c : Code) (n : Nat) :
    decodeConst c = some n → c = Code.const n := by
  induction c generalizing n with
  | zero =>
    intro h
    have : n = 0 := by simpa [decodeConst] using h.symm
    subst n
    rfl
  | succ => simp [decodeConst]
  | left => simp [decodeConst]
  | right => simp [decodeConst]
  | pair a b ia ib => simp [decodeConst]
  | prec a b ia ib => simp [decodeConst]
  | rfind' a ia => simp [decodeConst]
  | comp a b ia ib =>
    cases a with
    | zero => simp [decodeConst]
    | succ =>
      change (decodeConst b).map Nat.succ = some n → Code.comp Code.succ b = Code.const n
      rw [Option.map_eq_some_iff]
      rintro ⟨k, hk, rfl⟩
      simpa [Code.const] using congrArg (Code.comp Code.succ) (ib k hk)
    | left => simp [decodeConst]
    | right => simp [decodeConst]
    | pair x y => simp [decodeConst]
    | comp x y => simp [decodeConst]
    | prec x y => simp [decodeConst]
    | rfind' x => simp [decodeConst]

theorem decodeTerm_encodeTerm (t : Term) : decodeTerm (encodeTerm t) = some t := by
  induction t with
  | var n => simp [encodeTerm, decodeTerm, decodeConst_const]
  | abs t ih => simp [encodeTerm, decodeTerm, ih]
  | app a b ia ib => simp [encodeTerm, decodeTerm, ia, ib]


theorem decodeTerm_sound (c : Code) (t : Term) :
    decodeTerm c = some t → c = encodeTerm t := by
  induction c generalizing t with
  | zero => simp [decodeTerm]
  | succ => simp [decodeTerm]
  | left => simp [decodeTerm]
  | right => simp [decodeTerm]
  | comp a b ia ib => simp [decodeTerm]
  | prec a b ia ib =>
    cases a with
    | zero =>
      change (decodeConst b).map Term.var = some t → Code.prec Code.zero b = encodeTerm t
      rw [Option.map_eq_some_iff]
      rintro ⟨n, hn, rfl⟩
      simp [encodeTerm, decodeConst_sound b n hn]
    | succ => simp [decodeTerm]
    | left => simp [decodeTerm]
    | right => simp [decodeTerm]
    | pair x y => simp [decodeTerm]
    | comp x y => simp [decodeTerm]
    | prec x y => simp [decodeTerm]
    | rfind' x => simp [decodeTerm]
  | rfind' a ia =>
    change (decodeTerm a).map Term.abs = some t → Code.rfind' a = encodeTerm t
    rw [Option.map_eq_some_iff]
    rintro ⟨u, hu, rfl⟩
    simp [encodeTerm, ia u hu]
  | pair a b ia ib =>
    cases ha : decodeTerm a with
    | none => simp [decodeTerm, ha]
    | some x =>
      cases hb : decodeTerm b with
      | none => simp [decodeTerm, ha, hb]
      | some y =>
        intro h
        have he : Term.app x y = t := by simpa [decodeTerm, ha, hb] using h
        subst t
        simp [encodeTerm, ia x ha, ib y hb]

theorem decodeTerm_eq_some_iff (c : Code) (t : Term) :
    decodeTerm c = some t ↔ c = encodeTerm t := by
  constructor
  · exact decodeTerm_sound c t
  · rintro rfl
    exact decodeTerm_encodeTerm t

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro a b h
  have h' := congrArg decodeTerm h
  simpa only [decodeTerm_encodeTerm, Option.some.injEq] using h'



def foldConst (c : Code) : Option Nat :=
  Code.recOn c (some 0) none none none
    (fun _ _ _ _ => none)
    (fun f _ _ rec => if Encodable.encode f = Encodable.encode Code.succ then rec.map Nat.succ else none)
    (fun _ _ _ _ => none)
    (fun _ _ => none)

theorem foldConst_eq_decodeConst (c : Code) : foldConst c = decodeConst c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair a b ia ib => rfl
  | prec a b ia ib => rfl
  | rfind' a ia => rfl
  | comp a b ia ib =>
    simp only [foldConst] at ib
    cases a <;> simp [foldConst, decodeConst, ib, Encodable.encode_injective.eq_iff]

theorem primrec_foldConst : Primrec foldConst := by
  have hco : Primrec₂ (fun (_ : Code) (p : Code × Code × Option Nat × Option Nat) =>
      if Encodable.encode p.1 = Encodable.encode Code.succ then p.2.2.2.map Nat.succ else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const (Encodable.encode Code.succ))
    · exact (Primrec.option_map₁ Primrec.succ).comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const none
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => some 0)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ _ => none)
    (co := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.succ then p.2.2.2.map Nat.succ else none)
    (pc := fun _ _ => none) (rf := fun _ _ => none)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec₂.const _) hco (Primrec₂.const _) (Primrec₂.const _)
  exact h.of_eq (fun c => by rfl)

theorem primrec_decodeConst : Primrec decodeConst :=
  primrec_foldConst.of_eq foldConst_eq_decodeConst


/-- Decide whether a recursive-code tree is a canonical encoded lambda term. -/
def validCode (c : Code) : Bool :=
  Code.recOn c false false false false
    (fun _ _ ra rb => ra && rb)
    (fun _ _ _ _ => false)
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then (decodeConst g).isSome else false)
    (fun _ rec => rec)

theorem primrec_validCode : Primrec validCode := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × Bool × Bool) => p.2.2.1 && p.2.2.2) := by
    exact Primrec.and.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hpc : Primrec₂ (fun (_ : Code) (p : Code × Code × Bool × Bool) =>
      if Encodable.encode p.1 = Encodable.encode Code.zero then (decodeConst p.2.1).isSome else false) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const (Encodable.encode Code.zero))
    · exact Primrec.option_isSome.comp (primrec_decodeConst.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const false
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => false)
    (s := fun _ : Code => false) (l := fun _ : Code => false) (r := fun _ : Code => false)
    (pr := fun _ p => p.2.2.1 && p.2.2.2)
    (co := fun _ _ => false)
    (pc := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.zero then (decodeConst p.2.1).isSome else false)
    (rf := fun _ p => p.2)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc (Primrec₂.mk (Primrec.snd.comp Primrec.snd))
  exact h.of_eq (fun c => by rfl)

theorem validCode_decodeTerm (c : Code) : validCode c = (decodeTerm c).isSome := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | comp a b ia ib => rfl
  | pair a b ia ib =>
    change (validCode a && validCode b) = (decodeTerm (Code.pair a b)).isSome
    cases ha : decodeTerm a <;> cases hb : decodeTerm b <;>
      simp [decodeTerm, ia, ib, ha, hb]
  | rfind' a ia =>
    change validCode a = ((decodeTerm a).map Term.abs).isSome
    cases ha : decodeTerm a <;> simp [ia, ha]
  | prec a b ia ib =>
    cases a <;> simp [validCode, decodeTerm, Encodable.encode_injective.eq_iff]

theorem validCode_iff (c : Code) : validCode c = true ↔ ∃ t, c = encodeTerm t := by
  rw [validCode_decodeTerm, Option.isSome_iff_exists]
  exact exists_congr fun t => decodeTerm_eq_some_iff c t


theorem validCode_primrecPred : PrimrecPred (fun c => validCode c = true) := by
  apply Primrec.primrecPred
  convert primrec_validCode using 1
  funext c
  cases validCode c <;> simp

abbrev ValidCode := { c : Code // validCode c = true }

instance : Primcodable ValidCode := Primcodable.subtype validCode_primrecPred

/-- Term syntax is equivalent to the primitive-recursively recognized code image. -/
noncomputable def termEquivValid : Term ≃ ValidCode where
  toFun t := ⟨encodeTerm t, (validCode_iff _).2 ⟨t, rfl⟩⟩
  invFun c := Classical.choose ((validCode_iff c.val).1 c.property)
  left_inv t := by
    apply encodeTerm_injective
    exact (Classical.choose_spec ((validCode_iff (encodeTerm t)).1
      ((validCode_iff (encodeTerm t)).2 ⟨t, rfl⟩))).symm
  right_inv c := by
    apply Subtype.ext
    exact (Classical.choose_spec ((validCode_iff c.val).1 c.property)).symm

/-- Effective coding for terms, induced by the explicit canonical code image. -/
noncomputable instance : Primcodable Term := Primcodable.ofEquiv ValidCode termEquivValid



theorem executableTermCode_valid (t : Term) : validCode (encodeTerm t) = true :=
  (validCode_iff _).2 ⟨t, rfl⟩

theorem executableTermDecode_left (t : Term) :
    (decodeTerm (encodeTerm t)).getD (.var 0) = t := by
  rw [decodeTerm_encodeTerm]
  rfl

theorem executableTermDecode_right (c : ValidCode) :
    (⟨encodeTerm ((decodeTerm c.val).getD (.var 0)),
      executableTermCode_valid _⟩ : ValidCode) = c := by
  apply Subtype.ext
  obtain ⟨t, ht⟩ := (validCode_iff c.val).1 c.property
  change encodeTerm ((decodeTerm c.val).getD (.var 0)) = c.val
  rw [ht, decodeTerm_encodeTerm]
  rfl

def executableTermEquivValid : Term ≃ ValidCode where
  toFun t := ⟨encodeTerm t, executableTermCode_valid t⟩
  invFun c := (decodeTerm c.val).getD (.var 0)
  left_inv := executableTermDecode_left
  right_inv := executableTermDecode_right

@[instance_reducible]
def executableTermPrimcodable : Primcodable Term :=
  Primcodable.ofEquiv ValidCode executableTermEquivValid

def executableTermEncode (t : Term) : Nat :=
  @Encodable.encode Term executableTermPrimcodable.toEncodable t

def closedNumeralAtZero (m : Nat) (t : Term) : Prop :=
  Scoped 0 t ∧ NumericalResult t 0 m





def rootReductions (f x : Term) : List Term :=
  match f with
  | .abs body => [substAt 0 x body]
  | _ => []

set_option bootstrap.genMatcherCode false in
/-- All one-step full-beta reducts, including those below binders. -/
def betaSteps : Term → List Term
  | .var _ => []
  | .abs body => (betaSteps body).map Term.abs
  | .app f x => rootReductions f x ++
      (betaSteps f).map (fun g => .app g x) ++
      (betaSteps x).map (Term.app f)


def normalOrderStep (t : Term) : Option Term := (betaSteps t).head?


def normalOrderRun (n : Nat) (t : Term) : Term :=
  Nat.rec (motive := fun _ => Term → Term) (fun z => z)
    (fun _ rec z => (normalOrderStep z).elim z rec) n t




def decodeChurchBody : Term → Option Nat
  | .var 0 => some 0
  | .app (.var 1) t => (decodeChurchBody t).map Nat.succ
  | _ => none

def decodeChurch (t : Term) : Option Nat :=
  Term.casesOn t (fun _ => none)
    (fun b => Term.casesOn b (fun _ => none) decodeChurchBody (fun _ _ => none))
    (fun _ _ => none)


def selfApply : Term := .abs (.app (.var 0) (.var 0))
def omegaTerm : Term := .app selfApply selfApply

def normalObservationStage (t : Term) (k : Nat) : Option (Option Nat) :=
  match normalOrderStep (normalOrderRun k t) with
  | Option.none => some (decodeChurch (normalOrderRun k t))
  | some _ => none


noncomputable def normalObservation (t : Term) : Part (Option Nat) :=
  Nat.rfindOpt (normalObservationStage t)


def etaObservationZero : Term := .abs (.abs (.abs (.app (.var 1) (.var 0))))


theorem primrec_normalOrderRun : Primrec₂ (fun t k => normalOrderRun k t) := by
  sorry

theorem normalObservationStage_primrec : Primrec₂ normalObservationStage := by
  sorry

theorem normalObservation_partrec : Partrec normalObservation := by
  sorry

theorem mem_normalObservation_iff (t : Term) (r : Option Nat) :
    r ∈ normalObservation t ↔
      ∃ u, Reaches t u ∧ (¬ ∃ v, Beta u v) ∧ decodeChurch u = r := by
  sorry

theorem normalObservation_numeral_iff (t : Term) (n : Nat) :
    some n ∈ normalObservation t ↔ Reaches t (church n) := by
  sorry

theorem normalObservation_nonnumeral_iff (t : Term) :
    none ∈ normalObservation t ↔
      (∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) ∧
        ¬ ∃ n, Reaches t (church n) := by
  sorry

theorem normalObservation_undefined_iff (t : Term) :
    normalObservation t = Part.none ↔
      ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v := by
  sorry

theorem etaObservationZero_observer : none ∈ normalObservation etaObservationZero := by
  sorry

theorem omega_normalObservation_undefined : normalObservation omegaTerm = Part.none := by
  sorry

end LambdaTuring
