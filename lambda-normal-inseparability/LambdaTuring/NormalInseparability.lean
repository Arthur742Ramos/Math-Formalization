/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.NormalObservation
public meta import LambdaTuring.NormalObservation
public import LambdaTuring.EffectiveLambdaRecursion
public meta import LambdaTuring.EffectiveLambdaRecursion
public import LambdaTuring.ChurchPairs
public meta import LambdaTuring.ChurchPairs
public import LambdaTuring.NumeralReduction
public meta import LambdaTuring.NumeralReduction
@[expose] public section
namespace LambdaTuring

/-- Closed programs whose normal form is not a Church numeral. -/
def ClosedNonnumericalNormal (t : Term) : Prop :=
  Scoped 0 t ∧ none ∈ normalObservation t

/-- Turn the zero/one numerical observation of a program into two distinct
normal-form outcomes. Closure is needed only for the source program. -/
def normalOutcomeMap (t : Term) : Term :=
  .app (.app (.app churchIsZero (.app t (church 0))) (church 0)) identityTerm

theorem normalOutcomeMap_primrec : Primrec normalOutcomeMap := by
  have input : Primrec (fun t : Term => Term.app t (church 0)) :=
    primrec_app.comp Primrec.id (Primrec.const (church 0))
  exact primrec_app.comp
    (primrec_app.comp (primrec_app.comp (Primrec.const churchIsZero) input)
      (Primrec.const (church 0))) (Primrec.const identityTerm)

theorem normalOutcomeMap_closed {t : Term} (ht : Scoped 0 t) :
    Scoped 0 (normalOutcomeMap t) := by
  exact ⟨⟨⟨churchIsZero_closed, ⟨ht, church_closed 0⟩⟩, church_closed 0⟩,
    by simp [identityTerm, Scoped]⟩

theorem normalOutcomeMap_zero {t : Term} (h : NumericalResult t 0 0) :
    Reaches (normalOutcomeMap t) (church 0) := by
  have htest := reaches_trans (reaches_appRight churchIsZero h) (churchIsZero_run 0)
  have happ := reaches_appLeft (reaches_appLeft htest (church 0)) identityTerm
  exact reaches_trans happ (pairFirstSelector_run (church_closed 0) identityTerm)

theorem normalOutcomeMap_one {t : Term} (h : NumericalResult t 0 1) :
    Reaches (normalOutcomeMap t) identityTerm := by
  have htest := reaches_trans (reaches_appRight churchIsZero h) (churchIsZero_run 1)
  have happ := reaches_appLeft (reaches_appLeft htest (church 0)) identityTerm
  simp only [Nat.one_ne_zero, ite_false] at happ
  exact reaches_trans happ (pairSecondSelector_run (church 0) identityTerm)

theorem identityTerm_ne_church (n : Nat) : identityTerm ≠ church n := by
  simp [identityTerm, church]

theorem normalOutcomeMap_maps_zero {t : Term} (h : closedNumeralAtZero 0 t) :
    ClosedNumeralReach (normalOutcomeMap t) := by
  exact ⟨normalOutcomeMap_closed h.1, 0, normalOutcomeMap_zero h.2⟩

theorem normalOutcomeMap_maps_one {t : Term} (h : closedNumeralAtZero 1 t) :
    ClosedNonnumericalNormal (normalOutcomeMap t) := by
  refine ⟨normalOutcomeMap_closed h.1, (normalObservation_nonnumeral_iff _).2 ?_⟩
  have hid := normalOutcomeMap_one h.2
  refine ⟨⟨identityTerm, hid, identity_no_beta⟩, ?_⟩
  rintro ⟨n, hnum⟩
  exact identityTerm_ne_church n (normal_forms_unique hid hnum identity_no_beta (church_no_beta n))

theorem normalLanguages_disjoint (t : Term) :
    ¬ (ClosedNumeralReach t ∧ ClosedNonnumericalNormal t) := by
  rintro ⟨⟨_, n, hn⟩, ⟨_, hnone⟩⟩
  exact ((normalObservation_nonnumeral_iff t).1 hnone).2 ⟨n, hn⟩

/-- A fixed code for the partial-recursive preimage evaluator gives a
primitive-recursive recognizer-code transformer. -/
theorem normalOutcomeMap_recognizer_codes :
    ∃ q : Nat.Partrec.Code → Nat.Partrec.Code, Primrec q ∧
      ∀ c t, codeAcceptsTerm (q c) t ↔ codeAcceptsTerm c (normalOutcomeMap t) := by
  have henc : Computable executableTermEncode :=
    (Primrec.encode.of_eq (fun t => (executableTermEncode_eq t).symm)).to_comp
  have heval : Partrec (fun p : Nat.Partrec.Code × Term =>
      Nat.Partrec.Code.eval p.1 (executableTermEncode (normalOutcomeMap p.2))) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst
      (henc.comp (normalOutcomeMap_primrec.to_comp.comp Computable.snd))
  change Nat.Partrec (fun n => Part.bind
      (Part.ofOption (Encodable.decode (α := Nat.Partrec.Code × Term) n)) fun p =>
      (Nat.Partrec.Code.eval p.1 (executableTermEncode (normalOutcomeMap p.2))).map
        Encodable.encode) at heval
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp heval
  have hu' (c : Nat.Partrec.Code) (t : Term) :
      Nat.Partrec.Code.eval u (Nat.pair (Encodable.encode c) (executableTermEncode t)) =
        Nat.Partrec.Code.eval c (executableTermEncode (normalOutcomeMap t)) := by
    have h := congrFun hu (Encodable.encode (c, t))
    simpa [Encodable.encode_prod_val, executableTermEncode_eq, Part.map_id'] using h
  let q : Nat.Partrec.Code → Nat.Partrec.Code := fun c => Nat.Partrec.Code.curry u (Encodable.encode c)
  have hq : Primrec q := Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode
  refine ⟨q, hq, ?_⟩
  intro c t
  simp [codeAcceptsTerm, q, Nat.Partrec.Code.eval_curry, hu']

/-- Uniformly defeat any disjoint recursive recognizer supersets of the two
closed normal-form languages. The witness transformer is primitive recursive. -/
theorem normalLanguages_effectively_inseparable :
    ∃ productive : Nat.Partrec.Code × Nat.Partrec.Code → Term, Primrec productive ∧
      ∀ e f,
        (∀ t, ClosedNumeralReach t → codeAcceptsTerm e t) →
        (∀ t, ClosedNonnumericalNormal t → codeAcceptsTerm f t) →
        (∀ t, Scoped 0 t → ¬ (codeAcceptsTerm e t ∧ codeAcceptsTerm f t)) →
        Scoped 0 (productive (e, f)) ∧
          ¬ codeAcceptsTerm e (productive (e, f)) ∧
          ¬ codeAcceptsTerm f (productive (e, f)) := by
  obtain ⟨q, hq, hpre⟩ := normalOutcomeMap_recognizer_codes
  obtain ⟨p, hp, hprod⟩ := closedZeroOne_effectively_inseparable
  let productive : Nat.Partrec.Code × Nat.Partrec.Code → Term := fun z =>
    normalOutcomeMap (p (q z.1, q z.2))
  have hproductive : Primrec productive :=
    normalOutcomeMap_primrec.comp (hp.comp ((hq.comp Primrec.fst).pair (hq.comp Primrec.snd)))
  refine ⟨productive, hproductive, ?_⟩
  intro e f he hf hdis
  have hzero : ∀ t, closedNumeralAtZero 0 t → codeAcceptsTerm (q e) t := by
    intro t ht
    exact (hpre e t).2 (he _ (normalOutcomeMap_maps_zero ht))
  have hone : ∀ t, closedNumeralAtZero 1 t → codeAcceptsTerm (q f) t := by
    intro t ht
    exact (hpre f t).2 (hf _ (normalOutcomeMap_maps_one ht))
  have hdis' : ∀ t, Scoped 0 t → ¬ (codeAcceptsTerm (q e) t ∧ codeAcceptsTerm (q f) t) := by
    intro t ht hboth
    exact hdis _ (normalOutcomeMap_closed ht) ⟨(hpre e t).1 hboth.1, (hpre f t).1 hboth.2⟩
  obtain ⟨hclosed, hne, hnf⟩ := hprod (q e) (q f) hzero hone hdis'
  exact ⟨normalOutcomeMap_closed hclosed,
    fun h => hne ((hpre e _).2 h), fun h => hnf ((hpre f _).2 h)⟩

/-- Accept exactly the defined nonnumerical outcome of the normal observer. -/
noncomputable def nonnumericalOutcomeSearch (t : Term) : Part Unit :=
  (normalObservation t).bind fun r => if r = none then Part.some () else Part.none

theorem nonnumericalOutcomeSearch_partrec : Partrec nonnumericalOutcomeSearch := by
  have htest : Computable (fun p : Term × Option Nat => decide (p.2 = none)) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const none)).decide.to_comp
  have hbranch : Partrec (fun p : Term × Option Nat =>
      if p.2 = none then Part.some () else Part.none) := by
    apply (Partrec.cond htest (Partrec.some.comp (Computable.const ())) Partrec.none).of_eq
    intro p
    simp only [Bool.cond_eq_ite, decide_eq_true_eq]
  exact Partrec.bind normalObservation_partrec hbranch.to₂

theorem nonnumericalOutcomeSearch_dom (t : Term) :
    (nonnumericalOutcomeSearch t).Dom ↔ none ∈ normalObservation t := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 h
    obtain ⟨r, hr, hbranch⟩ := Part.mem_bind_iff.1 hv
    cases r with
    | none => exact hr
    | some n => simp at hbranch
  · intro h
    apply Part.dom_iff_mem.2
    exact ⟨(), Part.mem_bind_iff.2 ⟨none, h, by simp⟩⟩

theorem closedNonnumericalNormal_re : REPred ClosedNonnumericalNormal := by
  let closed : Term → Bool := fun t => decide (requiredDepth t ≤ 0)
  have hclosed : Computable closed :=
    (Primrec.nat_le.comp primrec_requiredDepth (Primrec.const 0)).decide.to_comp
  have hp : Partrec (fun t => cond (closed t) (nonnumericalOutcomeSearch t) Part.none) :=
    Partrec.cond hclosed nonnumericalOutcomeSearch_partrec Partrec.none
  apply hp.dom_re.of_eq
  intro t
  by_cases h : requiredDepth t = 0
  · have hs : Scoped 0 t := (scoped_iff_requiredDepth_le t 0).2 (by omega)
    simp [closed, ClosedNonnumericalNormal, h, hs, nonnumericalOutcomeSearch_dom]
  · have hs : ¬ Scoped 0 t := fun hs => h (by have := (scoped_iff_requiredDepth_le t 0).1 hs; omega)
    simp [closed, ClosedNonnumericalNormal, h, hs]

/-- No total computable Boolean test separates the two closed normal-form
languages, including when the test's behavior elsewhere is arbitrary. -/
theorem no_computable_normal_outcome_separator :
    ¬ ∃ d : Term → Bool, Computable d ∧
      (∀ t, ClosedNumeralReach t → d t = true) ∧
      (∀ t, ClosedNonnumericalNormal t → d t = false) := by
  rintro ⟨d, hd, hnum, hnon⟩
  apply no_computable_zero_one_separator (fun t => d (normalOutcomeMap t))
    (hd.comp normalOutcomeMap_primrec.to_comp)
  · intro t ht hz
    exact hnum _ (normalOutcomeMap_maps_zero ⟨ht, hz⟩)
  · intro t ht ho
    exact hnon _ (normalOutcomeMap_maps_one ⟨ht, ho⟩)

/-- The two disjoint closed normal-form languages are r.e. and effectively
inseparable, with a primitive-recursive productive witness. -/
theorem normalLanguages_re_effectively_inseparable :
    REPred ClosedNumeralReach ∧ REPred ClosedNonnumericalNormal ∧
      (∀ t, ¬ (ClosedNumeralReach t ∧ ClosedNonnumericalNormal t)) ∧
      ∃ productive : Nat.Partrec.Code × Nat.Partrec.Code → Term, Primrec productive ∧
        ∀ e f,
          (∀ t, ClosedNumeralReach t → codeAcceptsTerm e t) →
          (∀ t, ClosedNonnumericalNormal t → codeAcceptsTerm f t) →
          (∀ t, Scoped 0 t → ¬ (codeAcceptsTerm e t ∧ codeAcceptsTerm f t)) →
          Scoped 0 (productive (e, f)) ∧
            ¬ codeAcceptsTerm e (productive (e, f)) ∧
            ¬ codeAcceptsTerm f (productive (e, f)) := by
  exact ⟨closedNumeralReach_re, closedNonnumericalNormal_re,
    normalLanguages_disjoint, normalLanguages_effectively_inseparable⟩

#print axioms normalOutcomeMap_primrec
#print axioms normalOutcomeMap_maps_zero
#print axioms normalOutcomeMap_maps_one
#print axioms normalLanguages_disjoint
#print axioms normalOutcomeMap_recognizer_codes
#print axioms normalLanguages_effectively_inseparable
#print axioms closedNonnumericalNormal_re
#print axioms no_computable_normal_outcome_separator
#print axioms normalLanguages_re_effectively_inseparable

end LambdaTuring
