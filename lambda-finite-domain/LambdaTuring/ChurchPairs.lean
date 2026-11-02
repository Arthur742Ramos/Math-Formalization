/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSComposition
public meta import LambdaTuring.CPSComposition
public import LambdaTuring.ChurchSuccessor
public meta import LambdaTuring.ChurchSuccessor

@[expose] public section

/- Church-pair and iteration constructions follow the related Isabelle
   Lambda_Church_Pairs theory. These term pairs are not Mathlib's numeric pairing. -/

namespace LambdaTuring

/-- A Church pair of closed terms. -/
def churchPair (a b : Term) : Term := .abs (.app (.app (.var 0) a) b)
def pairFirstSelector : Term := .abs (.abs (.var 1))
def pairSecondSelector : Term := .abs (.abs (.var 0))
def pairFirst : Term := .abs (.app (.var 0) pairFirstSelector)
def pairSecond : Term := .abs (.app (.var 0) pairSecondSelector)

theorem churchPair_closed {a b : Term} (ha : Scoped 0 a) (hb : Scoped 0 b) :
    Scoped 0 (churchPair a b) := by
  change Scoped 1 (.app (.app (.var 0) a) b)
  exact ⟨⟨by simp [Scoped], scoped_mono ha (Nat.zero_le 1)⟩, scoped_mono hb (Nat.zero_le 1)⟩

theorem pairFirstSelector_closed : Scoped 0 pairFirstSelector := by simp [pairFirstSelector, Scoped]
theorem pairSecondSelector_closed : Scoped 0 pairSecondSelector := by simp [pairSecondSelector, Scoped]
theorem pairFirst_closed : Scoped 0 pairFirst := by simp [pairFirst, pairFirstSelector, Scoped]
theorem pairSecond_closed : Scoped 0 pairSecond := by simp [pairSecond, pairSecondSelector, Scoped]

theorem churchPair_apply {a b : Term} (ha : Scoped 0 a) (hb : Scoped 0 b) (k : Term) :
    Beta (.app (churchPair a b) k) (.app (.app k a) b) := by
  have hsa := substAt_scoped a 0 k ha
  have hsb := substAt_scoped b 0 k hb
  simpa [churchPair, substAt, liftBy, hsa, hsb] using
    (Beta.contract (.app (.app (.var 0) a) b) k)

theorem pairFirstSelector_run {a : Term} (ha : Scoped 0 a) (b : Term) :
    Reaches (.app (.app pairFirstSelector a) b) a := by
  have hl := liftFrom_scoped a 0 0 ha (le_refl _)
  have hs := substAt_scoped a 0 b ha
  have h1 : Beta (.app pairFirstSelector a) (.abs a) := by
    simpa [pairFirstSelector, substAt, liftBy, hl] using (Beta.contract (.abs (.var 1)) a)
  have h2 : Beta (.app (.abs a) b) a := by simpa [hs] using (Beta.contract a b)
  exact .step (.appLeft h1) (.step h2 (.refl _))

theorem pairSecondSelector_run (a b : Term) :
    Reaches (.app (.app pairSecondSelector a) b) b := by
  have h1 : Beta (.app pairSecondSelector a) (.abs (.var 0)) := by
    simpa [pairSecondSelector, substAt] using (Beta.contract (.abs (.var 0)) a)
  have h2 : Beta (.app (.abs (.var 0)) b) b := by
    simpa [substAt, liftBy] using (Beta.contract (.var 0) b)
  exact .step (.appLeft h1) (.step h2 (.refl _))

theorem pairFirst_run {a b : Term} (ha : Scoped 0 a) (hb : Scoped 0 b) :
    Reaches (.app pairFirst (churchPair a b)) a := by
  have hs := substAt_scoped pairFirstSelector 0 (churchPair a b) pairFirstSelector_closed
  have h1 : Beta (.app pairFirst (churchPair a b)) (.app (churchPair a b) pairFirstSelector) := by
    simpa [pairFirst, substAt, liftBy, hs] using
      (Beta.contract (.app (.var 0) pairFirstSelector) (churchPair a b))
  exact .step h1 (.step (churchPair_apply ha hb pairFirstSelector) (pairFirstSelector_run ha b))

theorem pairSecond_run {a b : Term} (ha : Scoped 0 a) (hb : Scoped 0 b) :
    Reaches (.app pairSecond (churchPair a b)) b := by
  have hs := substAt_scoped pairSecondSelector 0 (churchPair a b) pairSecondSelector_closed
  have h1 : Beta (.app pairSecond (churchPair a b)) (.app (churchPair a b) pairSecondSelector) := by
    simpa [pairSecond, substAt, liftBy, hs] using
      (Beta.contract (.app (.var 0) pairSecondSelector) (churchPair a b))
  exact .step h1 (.step (churchPair_apply ha hb pairSecondSelector) (pairSecondSelector_run a b))

/-- Iterate arbitrary terms, retaining full beta-reduction semantics. -/
def churchIter (n : Nat) (f z : Term) : Term :=
  match n with
  | 0 => z
  | n + 1 => .app f (churchIter n f z)

theorem subst_churchBody_function (n : Nat) (f : Term) :
    substAt 1 f (churchBody n) = churchIter n (liftFrom 0 f) (.var 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, churchIter, substAt, liftBy, ih]

theorem subst_churchIter_argument (n : Nat) (f z : Term) :
    substAt 0 z (churchIter n (liftFrom 0 f) (.var 0)) = churchIter n f z := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchIter, substAt, substAt_liftFrom, ih]

theorem church_iterates (n : Nat) (f z : Term) :
    Reaches (.app (.app (church n) f) z) (churchIter n f z) := by
  have hb1 : Beta (.app (church n) f) (.abs (churchIter n (liftFrom 0 f) (.var 0))) := by
    simpa [church, substAt, subst_churchBody_function] using (Beta.contract (.abs (churchBody n)) f)
  have hb2 : Beta (.app (.abs (churchIter n (liftFrom 0 f) (.var 0))) z) (churchIter n f z) := by
    simpa [subst_churchIter_argument] using (Beta.contract (churchIter n (liftFrom 0 f) (.var 0)) z)
  exact .step (.appLeft hb1) (.step hb2 (.refl _))

def indexedIteration (h : Nat → Nat → Nat) (base : Nat) : Nat → Nat
  | 0 => base
  | n + 1 => h n (indexedIteration h base n)

theorem churchPair_indexed_iteration (h : Nat → Nat → Nat) (S : Term)
    (step : ∀ i v, Reaches (.app S (churchPair (church i) (church v)))
      (churchPair (church (i + 1)) (church (h i v)))) (base n : Nat) :
    Reaches (churchIter n S (churchPair (church 0) (church base)))
      (churchPair (church n) (church (indexedIteration h base n))) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    exact reaches_trans (reaches_appRight S ih) (step n (indexedIteration h base n))

theorem church_numeral_indexed_iteration (h : Nat → Nat → Nat) (S : Term)
    (step : ∀ i v, Reaches (.app S (churchPair (church i) (church v)))
      (churchPair (church (i + 1)) (church (h i v)))) (base n : Nat) :
    Reaches (.app (.app (church n) S) (churchPair (church 0) (church base)))
      (churchPair (church n) (church (indexedIteration h base n))) :=
  reaches_trans (church_iterates n S (churchPair (church 0) (church base)))
    (churchPair_indexed_iteration h S step base n)

theorem liftBy_closed (n : Nat) {t : Term} (h : Scoped 0 t) : liftBy n t = t := by
  have hl : liftFrom 0 t = t := liftFrom_scoped t 0 0 h (le_refl _)
  induction n with
  | zero => rfl
  | succ n ih => simp [liftBy, ih, hl]

theorem churchIter_body (m n : Nat) :
    churchIter m (.var 1) (churchBody n) = churchBody (m + n) := by
  induction m with
  | zero => simp [churchIter]
  | succ m ih => simpa [churchIter, churchBody, Nat.succ_add] using congrArg (Term.app (.var 1)) ih

/-- Binary addition of Church numerals. -/
def churchAdd : Term :=
  .abs (.abs (.abs (.abs (.app (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0))))))

theorem churchAdd_closed : Scoped 0 churchAdd := by simp [churchAdd, Scoped]

theorem churchAdd_run (m n : Nat) :
    Reaches (.app (.app churchAdd (church m)) (church n)) (church (m + n)) := by
  have hmshift : liftBy 3 (church m) = church m := liftBy_closed 3 (church_closed m)
  have h1 : Beta (.app churchAdd (church m))
      (.abs (.abs (.abs (.app (.app (church m) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))))) := by
    simpa [churchAdd, substAt, hmshift] using
      (Beta.contract (.abs (.abs (.abs (.app (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))))) (church m))
  have hnshift : liftBy 2 (church n) = church n := liftBy_closed 2 (church_closed n)
  have hmsub := substAt_scoped (church m) 2 (church n) (scoped_mono (church_closed m) (Nat.zero_le 2))
  have h2 : Beta
      (.app (.abs (.abs (.abs (.app (.app (church m) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))))) (church n))
      (.abs (.abs (.app (.app (church m) (.var 1)) (.app (.app (church n) (.var 1)) (.var 0))))) := by
    simpa [substAt, hnshift, hmsub] using
      (Beta.contract (.abs (.abs (.app (.app (church m) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0))))) (church n))
  apply Reaches.step (.appLeft h1)
  apply Reaches.step h2
  apply reaches_trans (reaches_abs (reaches_abs (reaches_appRight (.app (church m) (.var 1)) (church_apply_vars n))))
  have h := church_iterates m (.var 1) (churchBody n)
  rw [churchIter_body] at h
  exact reaches_abs (reaches_abs h)

theorem churchIter_multiply (m n : Nat) :
    Reaches (churchIter m (.app (church n) (.var 1)) (.var 0)) (churchBody (m * n)) := by
  induction m with
  | zero => simpa [churchIter, churchBody] using Reaches.refl (.var 0)
  | succ m ih =>
    have h1 := reaches_appRight (.app (church n) (.var 1)) ih
    have h2 := church_iterates n (.var 1) (churchBody (m * n))
    rw [churchIter_body] at h2
    have h := reaches_trans h1 h2
    simpa [churchIter, Nat.succ_mul, Nat.add_comm] using h

/-- Binary multiplication of Church numerals. -/
def churchMultiply : Term :=
  .abs (.abs (.abs (.abs (.app (.app (.var 3) (.app (.var 2) (.var 1))) (.var 0)))))

theorem churchMultiply_closed : Scoped 0 churchMultiply := by simp [churchMultiply, Scoped]

theorem churchMultiply_run (m n : Nat) :
    Reaches (.app (.app churchMultiply (church m)) (church n)) (church (m * n)) := by
  have hmshift : liftBy 3 (church m) = church m := liftBy_closed 3 (church_closed m)
  have h1 : Beta (.app churchMultiply (church m))
      (.abs (.abs (.abs (.app (.app (church m) (.app (.var 2) (.var 1))) (.var 0))))) := by
    simpa [churchMultiply, substAt, hmshift] using
      (Beta.contract (.abs (.abs (.abs (.app (.app (.var 3) (.app (.var 2) (.var 1))) (.var 0))))) (church m))
  have hnshift : liftBy 2 (church n) = church n := liftBy_closed 2 (church_closed n)
  have hmsub := substAt_scoped (church m) 2 (church n) (scoped_mono (church_closed m) (Nat.zero_le 2))
  have h2 : Beta
      (.app (.abs (.abs (.abs (.app (.app (church m) (.app (.var 2) (.var 1))) (.var 0))))) (church n))
      (.abs (.abs (.app (.app (church m) (.app (church n) (.var 1))) (.var 0)))) := by
    simpa [substAt, hnshift, hmsub] using
      (Beta.contract (.abs (.abs (.app (.app (church m) (.app (.var 2) (.var 1))) (.var 0)))) (church n))
  apply Reaches.step (.appLeft h1)
  apply Reaches.step h2
  apply reaches_trans (reaches_abs (reaches_abs (church_iterates m (.app (church n) (.var 1)) (.var 0))))
  exact reaches_abs (reaches_abs (churchIter_multiply m n))

/-- Exact numerical representation for a closed binary Church program. -/
def BinaryRepresents (t : Term) (f : Nat → Nat → Nat) : Prop :=
  Scoped 0 t ∧ ∀ a b m, Reaches (.app (.app t (church a)) (church b)) (church m) ↔ m = f a b

theorem churchAdd_represents : BinaryRepresents churchAdd (· + ·) := by
  constructor
  · exact churchAdd_closed
  · intro a b m
    constructor
    · intro h
      exact numeral_result_unique h (churchAdd_run a b)
    · intro h
      subst m
      exact churchAdd_run a b

theorem churchMultiply_represents : BinaryRepresents churchMultiply (· * ·) := by
  constructor
  · exact churchMultiply_closed
  · intro a b m
    constructor
    · intro h
      exact numeral_result_unique h (churchMultiply_run a b)
    · intro h
      subst m
      exact churchMultiply_run a b

/-- Zero test with the standard Church booleans (the pair selectors). -/
def zeroStep : Term := .abs pairSecondSelector
def churchIsZero : Term := .abs (.app (.app (.var 0) zeroStep) pairFirstSelector)

theorem zeroStep_closed : Scoped 0 zeroStep := by
  change Scoped 1 pairSecondSelector
  exact scoped_mono pairSecondSelector_closed (Nat.zero_le 1)

theorem churchIsZero_closed : Scoped 0 churchIsZero := by
  change Scoped 1 (.app (.app (.var 0) zeroStep) pairFirstSelector)
  exact ⟨⟨by simp [Scoped], scoped_mono zeroStep_closed (Nat.zero_le 1)⟩,
    scoped_mono pairFirstSelector_closed (Nat.zero_le 1)⟩

theorem churchIsZero_run (n : Nat) :
    Reaches (.app churchIsZero (church n)) (if n = 0 then pairFirstSelector else pairSecondSelector) := by
  have hz := substAt_scoped zeroStep 0 (church n) zeroStep_closed
  have ht := substAt_scoped pairFirstSelector 0 (church n) pairFirstSelector_closed
  have hb : Beta (.app churchIsZero (church n)) (.app (.app (church n) zeroStep) pairFirstSelector) := by
    simpa [churchIsZero, substAt, liftBy, hz, ht] using
      (Beta.contract (.app (.app (.var 0) zeroStep) pairFirstSelector) (church n))
  apply Reaches.step hb
  apply reaches_trans (church_iterates n zeroStep pairFirstSelector)
  cases n with
  | zero => exact .refl _
  | succ n =>
    have hs := substAt_scoped pairSecondSelector 0 (churchIter n zeroStep pairFirstSelector) pairSecondSelector_closed
    have hstep : Beta (.app zeroStep (churchIter n zeroStep pairFirstSelector)) pairSecondSelector := by
      have hcontract := Beta.contract pairSecondSelector (churchIter n zeroStep pairFirstSelector)
      rw [hs] at hcontract
      exact hcontract
    exact .step hstep (.refl _)

#print axioms pairFirst_run
#print axioms pairSecond_run
#print axioms church_iterates
#print axioms church_numeral_indexed_iteration
#print axioms churchAdd_run
#print axioms churchMultiply_run
#print axioms churchAdd_represents
#print axioms churchMultiply_represents
#print axioms churchIsZero_run

end LambdaTuring
