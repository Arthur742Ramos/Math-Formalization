/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.CPSContexts
public meta import LambdaTuring.CPSContexts
@[expose] public section

namespace LambdaTuring

/-- A weak-name evaluation annotated by its number of head contractions. -/
inductive WeakNameEvalCount : Nat → Term → Term → Prop where
  | abs (body : Term) : WeakNameEvalCount 0 (.abs body) body
  | app {nf nr : Nat} {f arg body result : Term} :
      WeakNameEvalCount nf f body →
      WeakNameEvalCount nr (substAt 0 arg body) result →
      WeakNameEvalCount (nf + nr + 1) (.app f arg) result

theorem WeakNameEvalCount.erase {n : Nat} {t body : Term}
    (h : WeakNameEvalCount n t body) : WeakNameEval t body := by
  induction h with
  | abs => exact .abs _
  | app _ _ ihf ihr => exact .app ihf ihr

theorem WeakNameEval.has_count {t body : Term} (h : WeakNameEval t body) :
    ∃ n, WeakNameEvalCount n t body := by
  induction h with
  | abs body => exact ⟨0, .abs body⟩
  | app _ _ ihf ihr =>
    obtain ⟨nf, hf⟩ := ihf
    obtain ⟨nr, hr⟩ := ihr
    exact ⟨nf + nr + 1, .app hf hr⟩

theorem WeakCBVSteps.append {m n : Nat} {a b c : Term}
    (h : WeakCBVSteps m a b) (k : WeakCBVSteps n b c) :
    WeakCBVSteps (m + n) a c := by
  induction h with
  | zero => simpa using k
  | succ hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WeakCBVSteps.succ hs (ih k)

/-- Exact target cost of a closed source evaluation, up to applying its
arbitrary abstraction continuation. -/
theorem WeakNameEvalCount.cps_forward {n : Nat} {t body : Term}
    (h : WeakNameEvalCount n t body) :
    Scoped 0 t → ∀ kbody,
      WeakCBVSteps (4 * n + 1) (.app (nameToValueCPS t) (.abs kbody))
        (.app (.abs kbody) (.abs (nameToValueCPS body))) := by
  induction h with
  | abs body =>
    intro _ kbody
    simpa using WeakCBVSteps.succ (nameToValueCPS_abs_enter body kbody) (.zero _)
  | @app nf nr f arg body result hf hr ihf ihr =>
    intro ht kbody
    have hfun : Scoped 0 f := ht.1
    have harg : Scoped 0 arg := ht.2
    have hbody : Scoped 1 body := cps_reaches_preserves_scope (weakNameEval_reaches hf.erase) hfun
    have hred : Scoped 0 (substAt 0 arg body) :=
      cps_scoped_substAt body arg 0 0 (by omega) hbody harg
    obtain ⟨argBody, hargValue⟩ := weakValue_exists_abs (nameToValueCPS_closed_value harg)
    have hbeta : WeakCBVStep (.app (.abs (nameToValueCPS body)) (nameToValueCPS arg))
        (nameToValueCPS (substAt 0 arg body)) := by
      rw [nameToValueCPS_substAt, hargValue]
      exact .beta _ _
    have hrest := ihr hred kbody
    have hdispatch := WeakCBVSteps.succ
      (cpsAppCont_dispatch (nameToValueCPS arg) (.abs kbody) (nameToValueCPS body))
      (WeakCBVSteps.succ (WeakCBVStep.appLeft hbeta) hrest)
    have hmid := (ihf hfun (cpsAppContBody (nameToValueCPS arg) (.abs kbody))).append hdispatch
    have hall := WeakCBVSteps.succ (nameToValueCPS_app_enter f arg kbody) hmid
    convert hall using 1; omega

/-- A finite sequence of weak call-by-name head contractions with its length. -/
inductive WeakHeadSteps : Nat → Term → Term → Prop where
  | zero (t : Term) : WeakHeadSteps 0 t t
  | succ {n : Nat} {a b c : Term} : HeadContract a b → WeakHeadSteps n b c →
      WeakHeadSteps (n + 1) a c

theorem WeakHeadSteps.append {m n : Nat} {a b c : Term}
    (h : WeakHeadSteps m a b) (k : WeakHeadSteps n b c) :
    WeakHeadSteps (m + n) a c := by
  induction h with
  | zero => simpa using k
  | succ hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WeakHeadSteps.succ hs (ih k)

theorem WeakHeadSteps.appLeft {n : Nat} {f g : Term}
    (h : WeakHeadSteps n f g) (arg : Term) :
    WeakHeadSteps n (.app f arg) (.app g arg) := by
  induction h with
  | zero => exact .zero _
  | succ hs _ ih => exact .succ (.appLeft arg hs) ih

theorem WeakNameEvalCount.head_steps {n : Nat} {t body : Term}
    (h : WeakNameEvalCount n t body) : WeakHeadSteps n t (.abs body) := by
  induction h with
  | abs => exact .zero _
  | @app nf nr f arg body result hf hr ihf ihr =>
    have hr' := WeakHeadSteps.succ (HeadContract.root body arg) ihr
    have hall := (ihf.appLeft arg).append hr'
    simpa [Nat.add_assoc] using hall

theorem WeakNameEvalCount.cps_identity {n : Nat} {t body : Term}
    (h : WeakNameEvalCount n t body) (ht : Scoped 0 t) :
    WeakCBVSteps (4 * n + 2) (.app (nameToValueCPS t) identityTerm)
      (.abs (nameToValueCPS body)) := by
  have hfirst := h.cps_forward ht (.var 0)
  have hid : WeakCBVStep (.app identityTerm (.abs (nameToValueCPS body)))
      (.abs (nameToValueCPS body)) := by
    simpa [identityTerm, substAt, liftBy] using
      (WeakCBVStep.beta (.var 0) (nameToValueCPS body))
  have hall := hfirst.append (WeakCBVSteps.succ hid (.zero _))
  simpa [identityTerm, Nat.add_assoc] using hall

theorem WeakHeadSteps.toPath {n : Nat} {t u : Term} (h : WeakHeadSteps n t u) :
    Relation.ReflTransGen HeadContract t u := by
  induction h with
  | zero => exact .refl
  | succ hs _ ih => exact .head hs ih

theorem WeakHeadSteps.terminal_length_unique {m n : Nat} {t u v : Term}
    (h : WeakHeadSteps m t u) (hu : ¬ ∃ z, HeadContract u z)
    (k : WeakHeadSteps n t v) (hv : ¬ ∃ z, HeadContract v z) : m = n := by
  induction h generalizing n v with
  | zero t =>
    cases k with
    | zero => rfl
    | succ hs _ => exact False.elim (hu ⟨_, hs⟩)
  | @succ m a b c hs rest ih =>
    cases k with
    | zero => exact False.elim (hv ⟨_, hs⟩)
    | @succ n _ b' _ hs' rest' =>
      have eq := headContract_deterministic hs hs'
      subst b'
      have hlen := ih hu rest' hv
      omega

theorem WeakCBVSteps.terminal_length_unique {m n : Nat} {t u v : Term}
    (h : WeakCBVSteps m t u) (hu : WeakValue u)
    (k : WeakCBVSteps n t v) (hv : WeakValue v) : m = n := by
  induction h generalizing n v with
  | zero t =>
    cases k with
    | zero => rfl
    | succ hs _ => exact False.elim (weakValue_no_cbvStep hu ⟨_, hs⟩)
  | @succ m a b c hs rest ih =>
    cases k with
    | zero => exact False.elim (weakValue_no_cbvStep hv ⟨_, hs⟩)
    | @succ n _ b' _ hs' rest' =>
      have eq := weakCBVStep_deterministic hs hs'
      subst b'
      have hlen := ih hu rest' hv
      omega

theorem WeakCBVSteps.toPath {n : Nat} {t u : Term} (h : WeakCBVSteps n t u) :
    WeakCBVPath t u := by
  induction h with
  | zero => exact .refl _
  | succ hs _ ih => exact .step hs ih

/-- Exact beta-step cost for closed source programs. The source count is
weak head contractions; the target count is weak call-by-value contractions. -/
theorem cps_identity_exact_cost (t : Term) (ht : Scoped 0 t) (n : Nat) :
    (∃ body, WeakHeadSteps n t (.abs body)) ↔
      ∃ v, WeakCBVSteps (4 * n + 2) (.app (nameToValueCPS t) identityTerm) v ∧ WeakValue v := by
  constructor
  · rintro ⟨body, h⟩
    have heval := weakNameEval_headPath_backward h.toPath (WeakNameEval.abs body)
    obtain ⟨m, hm⟩ := heval.has_count
    have hlen := h.terminal_length_unique (by simp [headContract_abs_impossible])
      hm.head_steps (by simp [headContract_abs_impossible])
    subst m
    exact ⟨_, hm.cps_identity ht, .abs _⟩
  · rintro ⟨v, h, hv⟩
    obtain ⟨body, hhead, _⟩ := valueCPS_reflect_exact ht h.toPath hv
    have heval := weakNameEval_headPath_backward hhead (WeakNameEval.abs body)
    obtain ⟨m, hm⟩ := heval.has_count
    have hlen := h.terminal_length_unique hv (hm.cps_identity ht) (.abs _)
    have eq : n = m := by omega
    subst m
    exact ⟨body, hm.head_steps⟩

/-- Exact cost for the existing translated source-context tests. The hole and
the plugged source program are closed; fixed side terms may be open. -/
theorem LambdaContext.cps_context_exact_cost (c : LambdaContext) (t : Term)
    (ht : Scoped 0 t) (hclosed : Scoped 0 (c.plug t)) (n : Nat) :
    (∃ body, WeakHeadSteps n (c.plug t) (.abs body)) ↔
      ∃ v, WeakCBVSteps (4 * n + 2)
        (.app (c.cps.plug (nameToValueCPS t)) identityTerm) v ∧ WeakValue v := by
  rw [LambdaContext.cps_plug_closed c t ht]
  exact cps_identity_exact_cost (c.plug t) hclosed n

#print axioms WeakNameEvalCount.cps_forward
#print axioms WeakNameEvalCount.head_steps
#print axioms WeakNameEvalCount.cps_identity
#print axioms cps_identity_exact_cost
#print axioms LambdaContext.cps_context_exact_cost
end LambdaTuring
