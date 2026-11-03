/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.NormalOrder
public meta import LambdaTuring.NormalOrder
public import LambdaTuring.Observation
public meta import LambdaTuring.Observation
public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom
@[expose] public section

namespace LambdaTuring

/-- Values of the closed, pure weak call-by-value language are abstractions. -/
inductive WeakValue : Term → Prop where
  | abs (body : Term) : WeakValue (.abs body)

/-- Left-to-right call-by-value does not reduce inside abstractions. -/
inductive WeakCBVStep : Term → Term → Prop where
  | appLeft {f g x : Term} : WeakCBVStep f g → WeakCBVStep (.app f x) (.app g x)
  | appRight {body x y : Term} : WeakCBVStep x y →
      WeakCBVStep (.app (.abs body) x) (.app (.abs body) y)
  | beta (body arg : Term) :
      WeakCBVStep (.app (.abs body) (.abs arg)) (substAt 0 (.abs arg) body)

theorem weakCBVStep_beta {t u : Term} (h : WeakCBVStep t u) : Beta t u := by
  induction h with
  | appLeft _ ih => exact .appLeft ih
  | appRight _ ih => exact .appRight ih
  | beta body arg => exact .contract _ _

theorem weakCBV_abs_no_step (body : Term) : ¬ ∃ u, WeakCBVStep (.abs body) u := by
  rintro ⟨u, h⟩
  cases h

theorem weakCBVStep_deterministic {t u v : Term}
    (hu : WeakCBVStep t u) (hv : WeakCBVStep t v) : u = v := by
  induction hu generalizing v with
  | @appLeft f g x h ih =>
    cases hv with
    | appLeft h' => exact congrArg (fun z => Term.app z x) (ih h')
    | appRight h' => exact False.elim (weakCBV_abs_no_step _ ⟨_, h⟩)
    | beta body arg => exact False.elim (weakCBV_abs_no_step _ ⟨_, h⟩)
  | @appRight body x y h ih =>
    cases hv with
    | appLeft h' => exact False.elim (weakCBV_abs_no_step _ ⟨_, h'⟩)
    | appRight h' => exact congrArg (Term.app (.abs body)) (ih h')
    | beta body arg => exact False.elim (weakCBV_abs_no_step _ ⟨_, h⟩)
  | beta body arg =>
    cases hv with
    | appLeft h' => exact False.elim (weakCBV_abs_no_step _ ⟨_, h'⟩)
    | appRight h' => exact False.elim (weakCBV_abs_no_step _ ⟨_, h'⟩)
    | beta => rfl

inductive WeakCBVPath : Term → Term → Prop where
  | refl (t : Term) : WeakCBVPath t t
  | step {a b c : Term} : WeakCBVStep a b → WeakCBVPath b c → WeakCBVPath a c

theorem weakCBVPath_beta {t u : Term} (h : WeakCBVPath t u) : Reaches t u := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (weakCBVStep_beta hs) ih

/-- A standard reduction to an abstraction has a head-contraction prefix to
an abstraction, followed by a reduction only inside its body. -/
theorem standardReduction_abstraction_prefix {t u : Term} (h : StandardReduction t u) :
    ∀ body, u = .abs body → ∃ body',
      Relation.ReflTransGen HeadContract t (.abs body') ∧ StandardReduction body' body := by
  induction h using StandardReduction.rec (motive_2 := fun _ _ _ => True) with
  | @var n xs ys hs _ =>
    intro body heq
    have hh := congrArg spineHead heq
    simp [spineHead_applySpine, spineHead] at hh
  | @abs body body' xs ys hb hs ih ihs =>
    intro target heq
    have hys : ys = [] := by
      have ha := congrArg spineArguments heq
      simpa [spineArguments_applySpine, spineArguments] using ha
    subst ys
    cases hs with
    | nil =>
      have hbody : body' = target := by simpa [applySpine] using heq
      subst body'
      exact ⟨body, .refl, hb⟩
  | @head body arg target xs hs ih =>
    intro result heq
    obtain ⟨body', hp, hbody⟩ := ih result heq
    exact ⟨body', .head (headContract_applySpine (.root body arg) xs) hp, hbody⟩
  | nil => trivial
  | cons => trivial

/-- Every call-by-value computation that reaches an abstraction also reaches
an abstraction under call-by-name; the resulting bodies are beta-related. -/
theorem cbv_value_implies_name_value {t body : Term}
    (h : WeakCBVPath t (.abs body)) : ∃ body',
      Relation.ReflTransGen HeadContract t (.abs body') ∧ Reaches body' body := by
  obtain ⟨body', hp, hb⟩ := standardReduction_abstraction_prefix
    (reaches_standardReduction (weakCBVPath_beta h)) body rfl
  exact ⟨body', hp, standardReduction_reaches hb⟩

theorem omega_weakCBV_self : WeakCBVStep omegaTerm omegaTerm := by
  simpa [omegaTerm, selfApply, substAt, liftBy] using
    (WeakCBVStep.beta (.app (.var 0) (.var 0)) (.app (.var 0) (.var 0)))

def discardOmega : Term := .app discardInput omegaTerm

theorem discardOmega_closed : Scoped 0 discardOmega := by
  exact ⟨by simp [discardInput, identityTerm, Scoped], omega_closed⟩

theorem discardOmega_name_step : HeadContract discardOmega identityTerm := by
  simpa [discardOmega, discardInput, identityTerm, substAt, liftBy] using
    (HeadContract.root identityTerm omegaTerm)

theorem discardOmega_cbv_step : WeakCBVStep discardOmega discardOmega :=
  .appRight omega_weakCBV_self

theorem discardOmega_cbv_step_eq {t : Term} (h : WeakCBVStep discardOmega t) :
    t = discardOmega := by
  exact (weakCBVStep_deterministic h discardOmega_cbv_step)

theorem discardOmega_cbv_path_eq {t : Term} (h : WeakCBVPath discardOmega t) :
    t = discardOmega := by
  have hs : ∀ {a b : Term}, WeakCBVPath a b → a = discardOmega → b = discardOmega := by
    intro a b h
    induction h with
    | refl => exact fun ha => ha
    | step hs _ ih =>
      intro ha
      cases ha
      exact ih (discardOmega_cbv_step_eq hs)
  exact hs h rfl

/-- A closed term normalizes under full normal order, reaches a value in one
weak-name step, and can take only a repeating step under weak call-by-value. -/
theorem closed_name_value_cbv_loop :
    Scoped 0 discardOmega ∧ HeadContract discardOmega identityTerm ∧
    (∃ k, normalOrderRun k discardOmega = identityTerm ∧
      normalOrderStep (normalOrderRun k discardOmega) = none) ∧
    WeakCBVStep discardOmega discardOmega ∧
    (∀ v, WeakCBVPath discardOmega v → ¬ WeakValue v) := by
  refine ⟨discardOmega_closed, discardOmega_name_step, ?_, discardOmega_cbv_step, ?_⟩
  · exact normalOrder_normalizes_to (.step (headContract_beta discardOmega_name_step) (.refl _)) identity_no_beta
  · intro v hv hvalue
    have heq := discardOmega_cbv_path_eq hv
    subst v
    cases hvalue

/-- Every finite call-by-value prefix of the separating term can continue. -/
theorem discardOmega_cbv_every_prefix_continues :
    ∀ v, WeakCBVPath discardOmega v → ∃ w, WeakCBVStep v w := by
  intro v hv
  rw [discardOmega_cbv_path_eq hv]
  exact ⟨_, discardOmega_cbv_step⟩

/-- The two strategies may return different abstraction syntax even when
both converge; the bodies are still related by full beta reduction. -/
def distinctValueExample : Term :=
  .app (.abs (.abs (.var 1))) (.app identityTerm identityTerm)

theorem distinctValueExample_name :
    HeadContract distinctValueExample (.abs (.app identityTerm identityTerm)) := by
  simpa [distinctValueExample, identityTerm, substAt, liftBy, liftFrom] using
    (HeadContract.root (.abs (.var 1)) (.app identityTerm identityTerm))

theorem distinctValueExample_cbv :
    WeakCBVPath distinctValueExample (.abs identityTerm) := by
  have hid : WeakCBVStep (.app identityTerm identityTerm) identityTerm := by
    simpa [identityTerm, substAt, liftBy] using (WeakCBVStep.beta (.var 0) (.var 0))
  have houter : WeakCBVStep (.app (.abs (.abs (.var 1))) identityTerm) (.abs identityTerm) := by
    simpa [identityTerm, substAt, liftBy, liftFrom] using
      (WeakCBVStep.beta (.abs (.var 1)) (.var 0))
  exact .step (.appRight hid) (.step houter (.refl _))

theorem distinctValueExample_values_differ :
    (.abs (.app identityTerm identityTerm) : Term) ≠ .abs identityTerm := by
  simp [identityTerm]

theorem distinctValueExample_closed : Scoped 0 distinctValueExample := by
  simp [distinctValueExample, identityTerm, Scoped]

#print axioms weakCBVStep_deterministic
#print axioms cbv_value_implies_name_value
#print axioms closed_name_value_cbv_loop
#print axioms distinctValueExample_cbv

/-- Call-by-name CPS: source variables denote target computations, source
abstractions deliver translated values, and source arguments are thunks. -/
def nameToValueCPS : Term → Term
  | .var i => .var i
  | .abs body =>
      .abs (.app (.var 0) (.abs (liftFrom 1 (nameToValueCPS body))))
  | .app f x =>
      .abs (.app (liftFrom 0 (nameToValueCPS f))
        (.abs (.app (.app (.var 0) (liftBy 2 (nameToValueCPS x))) (.var 1))))

/-- Weak call-by-value paths compose. -/
theorem weakCBVPath_trans {a b c : Term} (hab : WeakCBVPath a b)
    (hbc : WeakCBVPath b c) : WeakCBVPath a c := by
  induction hab with
  | refl => exact hbc
  | step hs _ ih => exact .step hs (ih hbc)

/-- Shifting a term's free indices preserves scope at the incremented depth. -/
theorem scoped_liftFrom_succ {t : Term} {depth : Nat} (ht : Scoped depth t) (cutoff : Nat) :
    Scoped (depth + 1) (liftFrom cutoff t) := by
  induction t generalizing depth cutoff with
  | var i =>
    change i < depth at ht
    by_cases h : i < cutoff <;> simp [liftFrom, Scoped, h] <;> omega
  | abs body ih =>
    change Scoped (depth + 1) body at ht
    change Scoped ((depth + 1) + 1) (liftFrom (cutoff + 1) body)
    exact ih ht (cutoff + 1)
  | app f x ihf ihx =>
    exact ⟨ihf ht.1 cutoff, ihx ht.2 cutoff⟩

/-- Translating does not introduce free source variables. -/
theorem nameToValueCPS_scoped {t : Term} {depth : Nat} (ht : Scoped depth t) :
    Scoped depth (nameToValueCPS t) := by
  induction t generalizing depth with
  | var i => exact ht
  | abs body ih =>
    have hb : Scoped (depth + 1) (nameToValueCPS body) := ih ht
    change Scoped (depth + 1) (.app (.var 0) (.abs (liftFrom 1 (nameToValueCPS body))))
    exact ⟨by simp [Scoped], scoped_liftFrom_succ hb 1⟩
  | app f x ihf ihx =>
    have hf : Scoped depth (nameToValueCPS f) := ihf ht.1
    have hx : Scoped depth (nameToValueCPS x) := ihx ht.2
    have hf' := scoped_liftFrom_succ hf 0
    have hx' := scoped_liftFrom_succ (scoped_liftFrom_succ hx 0) 0
    change Scoped (depth + 1)
      (.app (liftFrom 0 (nameToValueCPS f))
        (.abs (.app (.app (.var 0) (liftBy 2 (nameToValueCPS x))) (.var 1))))
    refine ⟨hf', ?_⟩
    change Scoped (depth + 2) (.app (.app (.var 0) (liftBy 2 (nameToValueCPS x))) (.var 1))
    exact ⟨⟨by simp [Scoped], by simpa [liftBy] using hx'⟩, by simp [Scoped]⟩

/-- A closed source expression translates to a target abstraction. -/
theorem nameToValueCPS_closed_value {t : Term} (ht : Scoped 0 t) :
    WeakValue (nameToValueCPS t) := by
  cases t with
  | var i => simp [Scoped] at ht
  | abs body => exact .abs _
  | app f x => exact .abs _

/-- The source-abstraction base case delivers its translated value to the
identity continuation in exactly two weak call-by-value steps. -/
theorem nameToValueCPS_abstraction (body : Term) :
    WeakCBVPath (.app (nameToValueCPS (.abs body)) identityTerm)
      (.abs (nameToValueCPS body)) := by
  have hfirst : WeakCBVStep (.app (nameToValueCPS (.abs body)) identityTerm)
      (.app identityTerm (.abs (nameToValueCPS body))) := by
    simpa [nameToValueCPS, identityTerm, substAt, liftBy, substAt_liftFrom] using
      (WeakCBVStep.beta (.app (.var 0) (.abs (liftFrom 1 (nameToValueCPS body)))) (.var 0))
  have hsecond : WeakCBVStep (.app identityTerm (.abs (nameToValueCPS body)))
      (.abs (nameToValueCPS body)) := by
    simpa [identityTerm, substAt, liftBy] using (WeakCBVStep.beta (.var 0) (nameToValueCPS body))
  exact .step hfirst (.step hsecond (.refl _))

/-- Commutation of two index shifts, inherited from the verified de Bruijn
bridge rather than postulated as a property of the CPS translation. -/
theorem cps_liftFrom_comm (t : Term) (l k : Nat) (h : l ≤ k) :
    liftFrom (k + 1) (liftFrom l t) = liftFrom l (liftFrom k t) := by
  apply to_injective
  simp only [to_liftFrom]
  have hk : k - l + l = k := by omega
  simpa only [hk] using
    (Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_comm
      (i := 1) (j := 1) (k := k - l) (l := l) (t := toUpstream t))

theorem nameToValueCPS_liftFrom (t : Term) (depth : Nat) :
    nameToValueCPS (liftFrom depth t) = liftFrom depth (nameToValueCPS t) := by
  induction t generalizing depth with
  | var i => simp [liftFrom, nameToValueCPS]
  | abs body ih =>
    simp only [liftFrom, nameToValueCPS, ih, Nat.zero_lt_succ, ite_true]
    rw [cps_liftFrom_comm (nameToValueCPS body) 1 (depth + 1) (by omega)]
  | app f x ihf ihx =>
    simp only [liftFrom, nameToValueCPS, ihf, ihx, liftBy, Nat.zero_lt_succ, ite_true]
    rw [cps_liftFrom_comm (nameToValueCPS f) 0 depth (by omega)]
    rw [cps_liftFrom_comm (liftFrom 0 (nameToValueCPS x)) 0 (depth + 1) (by omega)]
    rw [cps_liftFrom_comm (nameToValueCPS x) 0 depth (by omega)]
    have h : 1 < depth + 1 + 1 := by omega
    simp only [h, ite_true]

theorem nameToValueCPS_liftBy (n : Nat) (t : Term) :
    nameToValueCPS (liftBy n t) = liftBy n (nameToValueCPS t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [liftBy, nameToValueCPS_liftFrom, ih]

theorem cps_liftFrom_liftBy (t : Term) (n l : Nat) (h : l ≤ n) :
    liftFrom l (liftBy n t) = liftBy (n + 1) t := by
  induction n generalizing l with
  | zero =>
    have : l = 0 := by omega
    subst l
    rfl
  | succ n ih =>
    cases l with
    | zero => rfl
    | succ l =>
      change liftFrom (l + 1) (liftFrom 0 (liftBy n t)) = liftFrom 0 (liftBy (n + 1) t)
      rw [cps_liftFrom_comm (liftBy n t) 0 l (by omega), ih l (by omega)]

/-- Inserting a binder below the substituted position commutes with
capture-avoiding substitution, shifting that position by one. -/
theorem cps_substAt_liftFrom (t value : Term) (depth cutoff : Nat) (h : cutoff ≤ depth) :
    substAt (depth + 1) value (liftFrom cutoff t) = liftFrom cutoff (substAt depth value t) := by
  apply to_injective
  simp only [to_substAt, to_liftFrom]
  have hd : depth - cutoff + cutoff = depth := by omega
  have hv : Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre 1 cutoff
      (Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre depth 0 (toUpstream value)) =
      Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre (depth + 1) 0 (toUpstream value) := by
    have hv' := congrArg toUpstream (cps_liftFrom_liftBy value depth cutoff h)
    simpa only [to_liftFrom, to_liftBy] using hv'
  simpa only [hd, hv] using
    (Cslib.LambdaCalculus.Unscoped.Untyped.Term.sub_lift_zero
      (i := cutoff) (n := depth - cutoff) (t := toUpstream t)
      (u := Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre depth 0 (toUpstream value)))

/-- Translation respects capture-avoiding source substitution. -/
theorem nameToValueCPS_substAt (t value : Term) (depth : Nat) :
    nameToValueCPS (substAt depth value t) =
      substAt depth (nameToValueCPS value) (nameToValueCPS t) := by
  induction t generalizing depth with
  | var i =>
    by_cases h : i = depth
    · subst i
      simp [substAt, nameToValueCPS_liftBy, nameToValueCPS]
    · simp [substAt, nameToValueCPS, h]
  | abs body ih =>
    simp only [substAt, nameToValueCPS, ih]
    rw [cps_substAt_liftFrom (nameToValueCPS body) (nameToValueCPS value) (depth + 1) 1 (by omega)]
    simp
  | app f x ihf ihx =>
    simp only [substAt, nameToValueCPS, ihf, ihx]
    rw [cps_substAt_liftFrom (nameToValueCPS f) (nameToValueCPS value) depth 0 (by omega)]
    simp only [liftBy]
    rw [cps_substAt_liftFrom (liftFrom 0 (nameToValueCPS x)) (nameToValueCPS value) (depth + 1) 0 (by omega)]
    rw [cps_substAt_liftFrom (nameToValueCPS x) (nameToValueCPS value) depth 0 (by omega)]
    simp

theorem cps_scoped_liftBy {t : Term} {depth : Nat} (ht : Scoped depth t) (n : Nat) :
    Scoped (depth + n) (liftBy n t) := by
  induction n with
  | zero => simpa [liftBy] using ht
  | succ n ih =>
    have h := scoped_liftFrom_succ ih 0
    simpa [liftBy, Nat.add_assoc] using h

/-- Substitution preserves scope when the replacement is scoped outside the
binders crossed by the substitution depth. -/
theorem cps_scoped_substAt (t value : Term) (scope depth : Nat)
    (hd : depth ≤ scope) (ht : Scoped (scope + 1) t)
    (hv : Scoped (scope - depth) value) : Scoped scope (substAt depth value t) := by
  induction t generalizing scope depth with
  | var i =>
    change i < scope + 1 at ht
    by_cases he : i = depth
    · subst i
      simp only [substAt, ite_true]
      have h := cps_scoped_liftBy hv depth
      simpa [Nat.sub_add_cancel hd] using h
    · by_cases hl : depth < i
      · simp only [substAt, he, ite_false, hl, ite_true, Scoped]
        omega
      · simp only [substAt, he, ite_false, hl, Scoped]
        omega
  | abs body ih =>
    change Scoped (scope + 1 + 1) body at ht
    change Scoped (scope + 1) (substAt (depth + 1) value body)
    apply ih (scope + 1) (depth + 1) (by omega) ht
    simpa using hv
  | app f x ihf ihx =>
    exact ⟨ihf scope depth hd ht.1 hv, ihx scope depth hd ht.2 hv⟩

theorem cps_beta_preserves_scope {t u : Term} (h : Beta t u) {depth : Nat} :
    Scoped depth t → Scoped depth u := by
  induction h generalizing depth with
  | contract body value =>
    intro hs
    exact cps_scoped_substAt body value depth 0 (by omega) hs.1 hs.2
  | abs h ih =>
    intro hs
    exact ih hs
  | appLeft h ih =>
    intro hs
    exact ⟨ih hs.1, hs.2⟩
  | appRight h ih =>
    intro hs
    exact ⟨hs.1, ih hs.2⟩

theorem cps_reaches_preserves_scope {t u : Term} (h : Reaches t u) {depth : Nat} :
    Scoped depth t → Scoped depth u := by
  induction h with
  | refl => exact fun hs => hs
  | step hs _ ih => exact fun ht => ih (cps_beta_preserves_scope hs ht)

theorem weakCBVPath_appLeft {f g : Term} (h : WeakCBVPath f g) (x : Term) :
    WeakCBVPath (.app f x) (.app g x) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.appLeft hs) ih

/-- The argument and continuation are shifted under the value binder. -/
def cpsAppContBody (arg cont : Term) : Term :=
  .app (.app (.var 0) (liftFrom 0 arg)) (liftFrom 0 cont)

def cpsAppCont (arg cont : Term) : Term := .abs (cpsAppContBody arg cont)

theorem nameToValueCPS_app_enter (f arg kbody : Term) :
    WeakCBVStep (.app (nameToValueCPS (.app f arg)) (.abs kbody))
      (.app (nameToValueCPS f) (cpsAppCont (nameToValueCPS arg) (.abs kbody))) := by
  have hshift : substAt 1 (.abs kbody)
      (liftFrom 0 (liftFrom 0 (nameToValueCPS arg))) = liftFrom 0 (nameToValueCPS arg) := by
    simpa only [liftBy] using substAt_liftBy_two (nameToValueCPS arg) (.abs kbody)
  simpa [nameToValueCPS, cpsAppCont, cpsAppContBody, substAt, liftBy,
    substAt_liftFrom, hshift] using
    (WeakCBVStep.beta
      (.app (liftFrom 0 (nameToValueCPS f))
        (.abs (.app (.app (.var 0) (liftBy 2 (nameToValueCPS arg))) (.var 1)))) kbody)

theorem nameToValueCPS_abs_enter (body kbody : Term) :
    WeakCBVStep (.app (nameToValueCPS (.abs body)) (.abs kbody))
      (.app (.abs kbody) (.abs (nameToValueCPS body))) := by
  simpa [nameToValueCPS, substAt, liftBy, substAt_liftFrom] using
    (WeakCBVStep.beta (.app (.var 0) (.abs (liftFrom 1 (nameToValueCPS body)))) kbody)

theorem cpsAppCont_dispatch (arg cont valueBody : Term) :
    WeakCBVStep (.app (cpsAppCont arg cont) (.abs valueBody))
      (.app (.app (.abs valueBody) arg) cont) := by
  simpa [cpsAppCont, cpsAppContBody, substAt, liftBy, substAt_liftFrom] using
    (WeakCBVStep.beta (cpsAppContBody arg cont) valueBody)

theorem weakValue_exists_abs {t : Term} (h : WeakValue t) : ∃ b, t = .abs b := by
  cases h with
  | abs body => exact ⟨body, rfl⟩

/-- Big-step call-by-name evaluates only the function and substitutes its
unevaluated argument. -/
inductive WeakNameEval : Term → Term → Prop where
  | abs (body : Term) : WeakNameEval (.abs body) body
  | app {f arg body result : Term} : WeakNameEval f body →
      WeakNameEval (substAt 0 arg body) result → WeakNameEval (.app f arg) result

theorem weakNameEval_reaches {t body : Term} (h : WeakNameEval t body) :
    Reaches t (.abs body) := by
  induction h with
  | abs => exact .refl _
  | @app f arg body result hf hr ihf ihr =>
    exact reaches_trans (reaches_appLeft ihf arg) (.step (.contract body arg) ihr)

/-- Forward simulation for closed source terms, with any abstraction as the
target continuation. The source argument is passed as a target thunk. -/
theorem weakNameEval_cps_forward {t body : Term} (h : WeakNameEval t body) :
    Scoped 0 t → ∀ kbody,
      WeakCBVPath (.app (nameToValueCPS t) (.abs kbody))
        (.app (.abs kbody) (.abs (nameToValueCPS body))) := by
  induction h with
  | abs body =>
    intro _ kbody
    exact .step (nameToValueCPS_abs_enter body kbody) (.refl _)
  | @app f arg body result hf hr ihf ihr =>
    intro ht kbody
    have hfun : Scoped 0 f := ht.1
    have harg : Scoped 0 arg := ht.2
    have hbody : Scoped 1 body := cps_reaches_preserves_scope (weakNameEval_reaches hf) hfun
    have hred : Scoped 0 (substAt 0 arg body) :=
      cps_scoped_substAt body arg 0 0 (by omega) hbody harg
    obtain ⟨argBody, hargValue⟩ := weakValue_exists_abs (nameToValueCPS_closed_value harg)
    have hbeta : WeakCBVStep (.app (.abs (nameToValueCPS body)) (nameToValueCPS arg))
        (nameToValueCPS (substAt 0 arg body)) := by
      rw [nameToValueCPS_substAt, hargValue]
      exact .beta _ _
    apply WeakCBVPath.step (nameToValueCPS_app_enter f arg kbody)
    apply weakCBVPath_trans (ihf hfun (cpsAppContBody (nameToValueCPS arg) (.abs kbody)))
    apply WeakCBVPath.step (cpsAppCont_dispatch (nameToValueCPS arg) (.abs kbody) (nameToValueCPS body))
    apply WeakCBVPath.step (WeakCBVStep.appLeft hbeta)
    exact ihr hred kbody

theorem weakNameEval_head_backward {t u body : Term} (h : HeadContract t u)
    (hu : WeakNameEval u body) : WeakNameEval t body := by
  induction h generalizing body with
  | root arg value => exact .app (.abs arg) hu
  | appLeft x h ih =>
    cases hu with
    | app hf hr => exact .app (ih hf) hr

theorem weakNameEval_headPath_backward {t u body : Term}
    (h : Relation.ReflTransGen HeadContract t u) (hu : WeakNameEval u body) :
    WeakNameEval t body := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hu
  | head hs _ ih => exact weakNameEval_head_backward hs ih

theorem headPath_appLeft {f g : Term} (h : Relation.ReflTransGen HeadContract f g)
    (x : Term) : Relation.ReflTransGen HeadContract (.app f x) (.app g x) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hs _ ih => exact .head (.appLeft x hs) ih

theorem weakNameEval_headPath {t body : Term} (h : WeakNameEval t body) :
    Relation.ReflTransGen HeadContract t (.abs body) := by
  induction h with
  | abs => exact .refl
  | @app f arg body result hf hr ihf ihr =>
    exact (headPath_appLeft ihf arg).trans (.head (.root body arg) ihr)

theorem weakNameEval_iff_headPath (t body : Term) :
    WeakNameEval t body ↔ Relation.ReflTransGen HeadContract t (.abs body) := by
  constructor
  · exact weakNameEval_headPath
  · intro h
    exact weakNameEval_headPath_backward h (.abs body)

/-- For a closed source, every finite weak call-by-name evaluation to an
abstraction is simulated by weak call-by-value CPS with identity continuation. -/
theorem head_to_valueCPS_forward {t body : Term} (ht : Scoped 0 t)
    (h : Relation.ReflTransGen HeadContract t (.abs body)) :
    WeakCBVPath (.app (nameToValueCPS t) identityTerm) (.abs (nameToValueCPS body)) := by
  have heval : WeakNameEval t body := weakNameEval_headPath_backward h (.abs body)
  have hid : WeakCBVStep (.app identityTerm (.abs (nameToValueCPS body)))
      (.abs (nameToValueCPS body)) := by
    simpa [identityTerm, substAt, liftBy] using (WeakCBVStep.beta (.var 0) (nameToValueCPS body))
  exact weakCBVPath_trans (weakNameEval_cps_forward heval ht (.var 0)) (.step hid (.refl _))

/-- The translation repairs the checked strategy-separation example: its
target computation terminates even though direct call-by-value loops. -/
theorem discardOmega_cps_terminates :
    WeakCBVPath (.app (nameToValueCPS discardOmega) identityTerm) identityTerm ∧
      (∀ v, WeakCBVPath discardOmega v → ¬ WeakValue v) := by
  have hhead : Relation.ReflTransGen HeadContract discardOmega (.abs (.var 0)) :=
    .head discardOmega_name_step .refl
  have h := head_to_valueCPS_forward discardOmega_closed hhead
  refine ⟨?_, (closed_name_value_cbv_loop).2.2.2.2⟩
  simpa [identityTerm, nameToValueCPS] using h

/-- A length-indexed target path supports reflection by induction on actual
call-by-value steps, rather than an unbounded search or a divergence premise. -/
inductive WeakCBVSteps : Nat → Term → Term → Prop where
  | zero (t : Term) : WeakCBVSteps 0 t t
  | succ {n : Nat} {a b c : Term} : WeakCBVStep a b → WeakCBVSteps n b c →
      WeakCBVSteps (n + 1) a c

theorem weakCBVPath_has_length {t u : Term} (h : WeakCBVPath t u) :
    ∃ n, WeakCBVSteps n t u := by
  induction h with
  | refl => exact ⟨0, .zero _⟩
  | step hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ hs hn⟩

theorem weakValue_no_cbvStep {t : Term} (h : WeakValue t) : ¬ ∃ u, WeakCBVStep t u := by
  cases h with
  | abs body => exact weakCBV_abs_no_step body

theorem weakCBVSteps_cancel {n : Nat} {t u v : Term} (h : WeakCBVSteps n t v)
    (hv : WeakValue v) (hs : WeakCBVStep t u) :
    ∃ m, m < n ∧ WeakCBVSteps m u v := by
  cases h with
  | zero => exact False.elim (weakValue_no_cbvStep hv ⟨u, hs⟩)
  | @succ m a b c hfirst hrest =>
    have heq := weakCBVStep_deterministic hfirst hs
    subst u
    exact ⟨m, by omega, hrest⟩

/-- A source argument spine is represented by a stack of target continuations. -/
def cpsStack : List Term → Term
  | [] => identityTerm
  | arg :: rest => cpsAppCont (nameToValueCPS arg) (cpsStack rest)

theorem cpsStack_value (xs : List Term) : WeakValue (cpsStack xs) := by
  cases xs with
  | nil => exact .abs _
  | cons arg rest => exact .abs _

theorem cpsStack_is_abs (xs : List Term) : ∃ b, cpsStack xs = .abs b :=
  weakValue_exists_abs (cpsStack_value xs)

theorem cpsStack_app_step (f arg : Term) (xs : List Term) :
    WeakCBVStep (.app (nameToValueCPS (.app f arg)) (cpsStack xs))
      (.app (nameToValueCPS f) (cpsStack (arg :: xs))) := by
  obtain ⟨k, hk⟩ := cpsStack_is_abs xs
  simpa only [cpsStack, hk] using nameToValueCPS_app_enter f arg k

/-- Evaluating a source beta-redex consumes three target steps when its source
argument is closed; the translated argument is then a target value. -/
theorem cpsStack_beta_steps (body arg : Term) (xs : List Term) (ha : Scoped 0 arg) :
    WeakCBVSteps 3 (.app (nameToValueCPS (.abs body)) (cpsStack (arg :: xs)))
      (.app (nameToValueCPS (substAt 0 arg body)) (cpsStack xs)) := by
  obtain ⟨argBody, harg⟩ := weakValue_exists_abs (nameToValueCPS_closed_value ha)
  have hbeta : WeakCBVStep (.app (.abs (nameToValueCPS body)) (nameToValueCPS arg))
      (nameToValueCPS (substAt 0 arg body)) := by
    rw [nameToValueCPS_substAt, harg]
    exact .beta _ _
  have hfirst := nameToValueCPS_abs_enter body (cpsAppContBody (nameToValueCPS arg) (cpsStack xs))
  have hsecond := cpsAppCont_dispatch (nameToValueCPS arg) (cpsStack xs) (nameToValueCPS body)
  exact .succ hfirst (.succ hsecond (.succ (.appLeft hbeta) (.zero _)))

theorem weakCBVSteps_cancel_exact {n : Nat} {t u v : Term} (h : WeakCBVSteps n t v)
    (hv : WeakValue v) (hs : WeakCBVStep t u) :
    ∃ m, n = m + 1 ∧ WeakCBVSteps m u v := by
  cases h with
  | zero => exact False.elim (weakValue_no_cbvStep hv ⟨u, hs⟩)
  | @succ m a b c hfirst hrest =>
    have heq := weakCBVStep_deterministic hfirst hs
    subst u
    exact ⟨m, rfl, hrest⟩

theorem weakCBVSteps_strip {k n : Nat} {a b v : Term} (hp : WeakCBVSteps k a b)
    (h : WeakCBVSteps n a v) (hv : WeakValue v) :
    ∃ m, n = m + k ∧ WeakCBVSteps m b v := by
  induction hp generalizing n with
  | zero => exact ⟨n, by simp, h⟩
  | @succ k a b c hs hp ih =>
    obtain ⟨m, hn, hm⟩ := weakCBVSteps_cancel_exact h hv hs
    obtain ⟨r, hr, hfinal⟩ := ih hm
    exact ⟨r, by omega, hfinal⟩

/-- If a translated closed term with a closed source-argument stack reaches a
target value, the corresponding source spine reaches an abstraction. -/
theorem cpsStack_reflect_value (n : Nat) :
    ∀ t xs v, Scoped 0 t → (∀ a ∈ xs, Scoped 0 a) → WeakValue v →
      WeakCBVSteps n (.app (nameToValueCPS t) (cpsStack xs)) v →
      ∃ body, Relation.ReflTransGen HeadContract (applySpine t xs) (.abs body) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t xs v ht hxs hv hrun
    cases t with
    | var i => simp [Scoped] at ht
    | app f arg =>
      have hstep := cpsStack_app_step f arg xs
      obtain ⟨m, hm, hrest⟩ := weakCBVSteps_cancel hrun hv hstep
      have hargs : ∀ a ∈ arg :: xs, Scoped 0 a := by
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact ht.2
        · exact hxs a ha
      have hresult := ih m hm f (arg :: xs) v ht.1 hargs hv hrest
      simpa [applySpine] using hresult
    | abs body =>
      cases xs with
      | nil => exact ⟨body, .refl⟩
      | cons arg xs =>
        have harg : Scoped 0 arg := hxs arg (by simp)
        have hrest : ∀ a ∈ xs, Scoped 0 a := by
          intro a ha
          exact hxs a (by simp [ha])
        have hp := cpsStack_beta_steps body arg xs harg
        obtain ⟨m, hm, hrun'⟩ := weakCBVSteps_strip hp hrun hv
        have hlt : m < n := by omega
        have hscope : Scoped 0 (substAt 0 arg body) :=
          cps_scoped_substAt body arg 0 0 (by omega) ht harg
        obtain ⟨result, hresult⟩ := ih m hlt (substAt 0 arg body) xs v hscope hrest hv hrun'
        refine ⟨result, ?_⟩
        exact .head (headContract_applySpine (.root body arg) xs) hresult

theorem weakCBVPath_value_unique {t u v : Term}
    (h : WeakCBVPath t u) (h' : WeakCBVPath t v)
    (hu : WeakValue u) (hv : WeakValue v) : u = v := by
  induction h generalizing v with
  | refl =>
    cases h' with
    | refl => rfl
    | step hs _ => exact False.elim (weakValue_no_cbvStep hu ⟨_, hs⟩)
  | @step a b c hs hp ih =>
    cases h' with
    | refl => exact False.elim (weakValue_no_cbvStep hv ⟨_, hs⟩)
    | @step _ d _ hs' hp' =>
      have heq := weakCBVStep_deterministic hs hs'
      subst d
      exact ih hp' hu hv

/-- Target value termination reflects to weak call-by-name convergence, and
determinism gives exact translated-value readback. -/
theorem valueCPS_reflect_exact {t v : Term} (ht : Scoped 0 t)
    (h : WeakCBVPath (.app (nameToValueCPS t) identityTerm) v) (hv : WeakValue v) :
    ∃ body, Relation.ReflTransGen HeadContract t (.abs body) ∧
      v = .abs (nameToValueCPS body) := by
  obtain ⟨n, hn⟩ := weakCBVPath_has_length h
  have hn' : WeakCBVSteps n (.app (nameToValueCPS t) (cpsStack [])) v := by
    simpa [cpsStack] using hn
  obtain ⟨body, hbody⟩ := cpsStack_reflect_value n t [] v ht (by simp) hv hn'
  have hhead : Relation.ReflTransGen HeadContract t (.abs body) := by simpa [applySpine] using hbody
  have hfwd := head_to_valueCPS_forward ht hhead
  exact ⟨body, hhead, weakCBVPath_value_unique h hfwd hv (.abs _)⟩

theorem valueCPS_terminates_iff_head_value (t : Term) (ht : Scoped 0 t) :
    (∃ v, WeakCBVPath (.app (nameToValueCPS t) identityTerm) v ∧ WeakValue v) ↔
      ∃ body, Relation.ReflTransGen HeadContract t (.abs body) := by
  constructor
  · rintro ⟨v, hv, hvalue⟩
    obtain ⟨body, hhead, _⟩ := valueCPS_reflect_exact ht hv hvalue
    exact ⟨body, hhead⟩
  · rintro ⟨body, hhead⟩
    exact ⟨_, head_to_valueCPS_forward ht hhead, .abs _⟩

#print axioms nameToValueCPS_scoped
#print axioms nameToValueCPS_abstraction
#print axioms nameToValueCPS_liftFrom
#print axioms nameToValueCPS_substAt
#print axioms weakNameEval_cps_forward
#print axioms head_to_valueCPS_forward
#print axioms discardOmega_cps_terminates
#print axioms cpsStack_reflect_value
#print axioms valueCPS_reflect_exact
#print axioms valueCPS_terminates_iff_head_value
end LambdaTuring
