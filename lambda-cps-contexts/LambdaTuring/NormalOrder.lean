/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.StandardReduction
public meta import LambdaTuring.StandardReduction
public import LambdaTuring.UniformLambdaEval
public meta import LambdaTuring.UniformLambdaEval
@[expose] public section

namespace LambdaTuring

/-- The existing enumeration lists the root redex first, then the function's
redexes, then the argument's, recursively descending below abstractions. -/
def normalOrderStep (t : Term) : Option Term := (betaSteps t).head?

theorem normalOrderStep_primrec : Primrec normalOrderStep := by
  have hs : Primrec betaSteps := primrec_betaSteps_of_subst primrec_substZero
  exact Primrec.list_head?.comp hs

theorem normalOrderStep_sound {t u : Term} (h : normalOrderStep t = some u) : Beta t u := by
  apply betaSteps_sound
  apply List.mem_of_mem_head?
  simpa [normalOrderStep, h]

theorem normalOrderStep_none_iff (t : Term) :
    normalOrderStep t = none ↔ ¬ ∃ u, Beta t u := by
  constructor
  · intro hn
    rintro ⟨u, hu⟩
    have hm := betaSteps_complete hu
    cases he : betaSteps t with
    | nil => simp [he] at hm
    | cons v vs => simp [normalOrderStep, he] at hn
  · intro hn
    cases he : normalOrderStep t with
    | none => rfl
    | some u => exact False.elim (hn ⟨u, normalOrderStep_sound he⟩)

@[simp] theorem normalOrderStep_var (i : Nat) : normalOrderStep (.var i) = none := by
  rfl

theorem normalOrderStep_abs (b : Term) :
    normalOrderStep (.abs b) = (normalOrderStep b).map Term.abs := by
  cases h : betaSteps b <;> simp [normalOrderStep, betaSteps, h]

theorem normalOrderStep_root (b x : Term) :
    normalOrderStep (.app (.abs b) x) = some (substAt 0 x b) := by
  simp [normalOrderStep, betaSteps, rootReductions]

theorem rootReductions_eq_nil_of_not_abs (f x : Term) (h : ¬ ∃ b, f = .abs b) :
    rootReductions f x = [] := by
  cases f with
  | var i => rfl
  | app f y => rfl
  | abs b => exact False.elim (h ⟨b, rfl⟩)

/-- With no root redex, reduce the function before the argument. -/
theorem normalOrderStep_app_left {f x u : Term} (hn : ¬ ∃ b, f = .abs b)
    (hf : normalOrderStep f = some u) :
    normalOrderStep (.app f x) = some (.app u x) := by
  have hr := rootReductions_eq_nil_of_not_abs f x hn
  cases h : betaSteps f with
  | nil => simp [normalOrderStep, h] at hf
  | cons v vs =>
    have hv : v = u := by simpa [normalOrderStep, h] using hf
    subst v
    simp [normalOrderStep, betaSteps, hr, h]

/-- With neither a root nor function redex, reduce the argument. -/
theorem normalOrderStep_app_right {f x u : Term} (hn : ¬ ∃ b, f = .abs b)
    (hf : normalOrderStep f = none) (hx : normalOrderStep x = some u) :
    normalOrderStep (.app f x) = some (.app f u) := by
  have hr := rootReductions_eq_nil_of_not_abs f x hn
  have hnil : betaSteps f = [] := by
    cases h : betaSteps f with
    | nil => rfl
    | cons v vs => simp [normalOrderStep, h] at hf
  cases h : betaSteps x with
  | nil => simp [normalOrderStep, h] at hx
  | cons v vs =>
    have hv : v = u := by simpa [normalOrderStep, h] using hx
    subst v
    simp [normalOrderStep, betaSteps, hr, hnil, h]

/-- Every existing weak-head contraction is the full normal-order choice. -/
theorem headContract_normalOrderStep {t u : Term} (h : HeadContract t u) :
    normalOrderStep t = some u := by
  induction h with
  | root body value => exact normalOrderStep_root body value
  | @appLeft f f' x h ih =>
    apply normalOrderStep_app_left ?_ ih
    rintro ⟨body, hbody⟩
    subst f
    exact headContract_abs_impossible h

/-- Finite, exact executions of the deterministic strategy. -/
inductive NormalOrderPath : Term → Term → Prop where
  | refl (t : Term) : NormalOrderPath t t
  | step {a b c : Term} : normalOrderStep a = some b → NormalOrderPath b c → NormalOrderPath a c

theorem normalOrderPath_trans {a b c : Term} (hab : NormalOrderPath a b)
    (hbc : NormalOrderPath b c) : NormalOrderPath a c := by
  induction hab with
  | refl => exact hbc
  | step hs _ ih => exact .step hs (ih hbc)

theorem normalOrderPath_reaches {a b : Term} (h : NormalOrderPath a b) : Reaches a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (normalOrderStep_sound hs) ih

theorem normalOrderPath_abs {a b : Term} (h : NormalOrderPath a b) :
    NormalOrderPath (.abs a) (.abs b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    apply NormalOrderPath.step ?_ ih
    simp [normalOrderStep_abs, hs]

/-- A variable-headed spine remains variable-headed after any beta step. -/
def VariableHead (t : Term) : Prop := ∃ n, spineHead t = .var n

theorem variableHead_not_abs {t : Term} (h : VariableHead t) : ¬ ∃ b, t = .abs b := by
  rintro ⟨b, rfl⟩
  obtain ⟨n, hn⟩ := h
  cases hn

theorem variableHead_beta {t u : Term} (h : Beta t u) : VariableHead t → VariableHead u := by
  induction h with
  | contract body value =>
    rintro ⟨n, hn⟩
    cases hn
  | abs h ih =>
    rintro ⟨n, hn⟩
    cases hn
  | appLeft h ih =>
    intro hv
    exact ih hv
  | appRight h ih =>
    intro hv
    exact hv

theorem normalOrderPath_app_left {f g : Term} (h : NormalOrderPath f g)
    (hf : VariableHead f) (x : Term) : NormalOrderPath (.app f x) (.app g x) := by
  induction h with
  | refl => exact .refl _
  | @step a b c hs _ ih =>
    apply NormalOrderPath.step (normalOrderStep_app_left (variableHead_not_abs hf) hs)
    exact ih (variableHead_beta (normalOrderStep_sound hs) hf)

theorem normalOrderPath_app_right {a b : Term} (h : NormalOrderPath a b)
    (f : Term) (hf : VariableHead f) (hfn : normalOrderStep f = none) :
    NormalOrderPath (.app f a) (.app f b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (normalOrderStep_app_right (variableHead_not_abs hf) hfn hs) ih

theorem variableHead_app {f : Term} (hf : VariableHead f) (x : Term) :
    VariableHead (.app f x) := hf

theorem normalOrderPath_spine {a b : Term} (h : NormalOrderPath a b)
    (ha : VariableHead a) (xs : List Term) :
    NormalOrderPath (applySpine a xs) (applySpine b xs) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    exact ih (normalOrderPath_app_left h ha x) (variableHead_app ha x)

theorem variableHead_app_normal {f x : Term} (hf : VariableHead f)
    (hfn : ¬ ∃ u, Beta f u) (hxn : ¬ ∃ u, Beta x u) :
    ¬ ∃ u, Beta (.app f x) u := by
  rintro ⟨u, hu⟩
  cases hu with
  | contract body value => exact variableHead_not_abs hf ⟨body, rfl⟩
  | appLeft h => exact hfn ⟨_, h⟩
  | appRight h => exact hxn ⟨_, h⟩

/-- Normalize a neutral spine's arguments in order. Later arguments are left
untouched until the preceding prefix is already in full beta-normal form. -/
theorem normalOrderPath_spine_arguments {xs ys : List Term}
    (hs : List.Forall₂ NormalOrderPath xs ys) :
    ∀ f, VariableHead f → (¬ ∃ u, Beta f u) →
      (∀ y ∈ ys, ¬ ∃ u, Beta y u) →
      NormalOrderPath (applySpine f xs) (applySpine f ys) := by
  induction hs with
  | nil =>
    intro f _ _ _
    exact .refl _
  | @cons x y xs ys hxy hrest ih =>
    intro f hf hfn hyn
    have hy : ¬ ∃ u, Beta y u := hyn y (by simp)
    have hys : ∀ y ∈ ys, ¬ ∃ u, Beta y u := by
      intro z hz
      exact hyn z (by simp [hz])
    have hfirst := normalOrderPath_app_right hxy f hf ((normalOrderStep_none_iff f).2 hfn)
    have hprefix := normalOrderPath_spine hfirst (variableHead_app hf x) xs
    have htail := ih (.app f y) (variableHead_app hf y) (variableHead_app_normal hf hfn hy) hys
    exact normalOrderPath_trans hprefix htail

theorem beta_applySpine_left {a b : Term} (h : Beta a b) (xs : List Term) :
    Beta (applySpine a xs) (applySpine b xs) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons x xs ih => exact ih (.appLeft h)

theorem beta_applySpine_argument (f : Term) (xs : List Term) {x y : Term}
    (hx : x ∈ xs) (hxy : Beta x y) : ∃ v, Beta (applySpine f xs) v := by
  induction xs generalizing f with
  | nil => simp at hx
  | cons z zs ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, beta_applySpine_left (.appRight hxy) zs⟩
    · exact ih (.app f z) hx

theorem normal_applySpine_arguments {f : Term} {xs : List Term}
    (hn : ¬ ∃ u, Beta (applySpine f xs) u) : ∀ x ∈ xs, ¬ ∃ u, Beta x u := by
  intro x hx
  rintro ⟨y, hy⟩
  exact hn (beta_applySpine_argument f xs hx hy)

/-- Standard reduction into a beta-normal form is executable in deterministic
normal order. The list induction normalizes spine arguments left to right. -/
theorem standardReduction_normalOrder {t n : Term} (h : StandardReduction t n) :
    (¬ ∃ u, Beta n u) → NormalOrderPath t n := by
  induction h using StandardReduction.rec
      (motive_2 := fun xs ys _ => (∀ y ∈ ys, ¬ ∃ u, Beta y u) →
        List.Forall₂ NormalOrderPath xs ys) with
  | @var n xs ys hs ihs =>
    intro hn
    have hy := normal_applySpine_arguments hn
    exact normalOrderPath_spine_arguments (ihs hy) (.var n) ⟨n, rfl⟩ (var_no_beta n) hy
  | @abs body body' xs ys hb hs ih ihs =>
    intro hn
    cases ys with
    | nil =>
      cases hs with
      | nil =>
        apply normalOrderPath_abs
        apply ih
        rintro ⟨v, hv⟩
        exact hn ⟨_, .abs hv⟩
    | cons y ys =>
      have hh := headContract_applySpine (HeadContract.root body' y) ys
      exact False.elim (hn ⟨_, headContract_beta hh⟩)
  | @head body arg target xs hs ih =>
    intro hn
    exact .step (headContract_normalOrderStep (headContract_applySpine (.root body arg) xs)) (ih hn)
  | nil =>
    exact .nil
  | @cons x y xs ys hxy hrest ihxy ihrest =>
    rename_i hn
    have hy : ¬ ∃ u, Beta y u := hn y (by simp)
    have hys : ∀ y ∈ ys, ¬ ∃ u, Beta y u := by
      intro z hz
      exact hn z (by simp [hz])
    exact .cons (ihxy hy) (ihrest hys)

/-- Head accessibility gives a finite strategy prefix ending at a term with
no weak-head step. It does not assert that this term is fully normal. -/
theorem headAccessible_normalOrder_prefix (t : Term) (h : HeadAccessible t) :
    ∃ u, NormalOrderPath t u ∧ ¬ ∃ v, HeadContract u v := by
  induction h with
  | intro t ha ih =>
    by_cases hex : ∃ u, HeadContract t u
    · obtain ⟨u, hu⟩ := hex
      obtain ⟨v, hv, hn⟩ := ih u hu
      exact ⟨v, .step (headContract_normalOrderStep hu) hv, hn⟩
    · exact ⟨t, .refl _, hex⟩

/-- If a full normal form exists, the strategy reaches a weak-head terminal
prefix from which that same full normal form is still beta-reachable. -/
theorem normalOrder_prefix_to_normal {t n : Term} (hn : Reaches t n)
    (hnormal : ¬ ∃ u, Beta n u) :
    ∃ u, NormalOrderPath t u ∧ (¬ ∃ v, HeadContract u v) ∧ Reaches u n := by
  have ha := standardReduction_headAccessible_of_normal (reaches_standardReduction hn) hnormal
  obtain ⟨u, hu, hhead⟩ := headAccessible_normalOrder_prefix t ha
  obtain ⟨v, huv, hnv⟩ := beta_confluent (normalOrderPath_reaches hu) hn
  have heq := normal_reaches_eq hnormal hnv
  subst v
  exact ⟨u, hu, hhead, huv⟩

/-- After a normal form is reached the bounded execution remains there. -/
def normalOrderRun (n : Nat) (t : Term) : Term :=
  Nat.rec (motive := fun _ => Term → Term) (fun z => z)
    (fun _ rec z => (normalOrderStep z).elim z rec) n t

theorem normalOrderRun_reaches (n : Nat) (t : Term) : Reaches t (normalOrderRun n t) := by
  induction n generalizing t with
  | zero => exact .refl _
  | succ n ih =>
    simp only [normalOrderRun]
    cases h : normalOrderStep t with
    | none => exact .refl _
    | some u => exact .step (normalOrderStep_sound h) (ih u)

theorem normalOrderPath_is_bounded_run {t u : Term} (h : NormalOrderPath t u) :
    ∃ n, normalOrderRun n t = u := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [normalOrderRun, hs, Option.elim_some]
    exact hn

/-- No reachable normal form implies every finite strategy prefix can take
another step; the converse is proved by the normal-order theorem below. -/
theorem normalOrder_never_stops_without_normal (t : Term)
    (hn : ¬ ∃ u, Reaches t u ∧ ¬ ∃ v, Beta u v) :
    ∀ n, ∃ u, normalOrderStep (normalOrderRun n t) = some u := by
  intro n
  cases h : normalOrderStep (normalOrderRun n t) with
  | none => exact False.elim (hn ⟨_, normalOrderRun_reaches n t, (normalOrderStep_none_iff _).1 h⟩)
  | some u => exact ⟨u, rfl⟩

/-- Normal order reaches any existing full beta-normal form. -/
theorem normalOrder_normalizes_to {t n : Term} (h : Reaches t n)
    (hn : ¬ ∃ u, Beta n u) :
    ∃ k, normalOrderRun k t = n ∧ normalOrderStep (normalOrderRun k t) = none := by
  have hs := standardReduction_normalOrder (reaches_standardReduction h) hn
  obtain ⟨k, hk⟩ := normalOrderPath_is_bounded_run hs
  refine ⟨k, hk, ?_⟩
  rw [hk]
  exact (normalOrderStep_none_iff n).2 hn

/-- Normal order stops exactly when a full beta-normal form is reachable. -/
theorem normalOrder_stops_iff_normalizable (t : Term) :
    (∃ k, normalOrderStep (normalOrderRun k t) = none) ↔
      ∃ n, Reaches t n ∧ ¬ ∃ u, Beta n u := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, normalOrderRun_reaches k t, (normalOrderStep_none_iff _).1 hk⟩
  · rintro ⟨n, hn, hnormal⟩
    obtain ⟨k, _, hk⟩ := normalOrder_normalizes_to hn hnormal
    exact ⟨k, hk⟩

/-- The deterministic strategy has a next step at every finite stage exactly
when no full beta-normal form is reachable. This does not assert that other
beta strategies diverge when a normal form exists. -/
theorem normalOrder_infinite_iff_not_normalizable (t : Term) :
    (∀ k, ∃ u, normalOrderStep (normalOrderRun k t) = some u) ↔
      ¬ ∃ n, Reaches t n ∧ ¬ ∃ u, Beta n u := by
  constructor
  · intro h hn
    obtain ⟨k, hk⟩ := (normalOrder_stops_iff_normalizable t).2 hn
    obtain ⟨u, hu⟩ := h k
    rw [hk] at hu
    cases hu
  · exact normalOrder_never_stops_without_normal t

/-- Any normal form reached by the strategy is the unique full-beta
normal form; normalization of the strategy is proved above. -/
theorem normalOrderRun_normal_unique (n : Nat) (t u : Term)
    (hn : normalOrderStep (normalOrderRun n t) = none)
    (hu : Reaches t u) (huNormal : ¬ ∃ v, Beta u v) : normalOrderRun n t = u := by
  have hnNormal := (normalOrderStep_none_iff _).1 hn
  obtain ⟨v, hnv, huv⟩ := beta_confluent (normalOrderRun_reaches n t) hu
  have ha := normal_reaches_eq hnNormal hnv
  have hb := normal_reaches_eq huNormal huv
  exact ha.trans hb.symm

#print axioms normalOrderStep_primrec
#print axioms normalOrderStep_none_iff
#print axioms headAccessible_normalOrder_prefix
#print axioms normalOrder_prefix_to_normal
#print axioms normalOrder_never_stops_without_normal
#print axioms standardReduction_normalOrder
#print axioms normalOrder_normalizes_to
#print axioms normalOrder_stops_iff_normalizable
#print axioms normalOrder_infinite_iff_not_normalizable
#print axioms normalOrderRun_normal_unique
end LambdaTuring
