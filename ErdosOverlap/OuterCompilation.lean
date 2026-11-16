/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.OuterSchema
public import ErdosOverlap.Numerics.FourierPolynomial

/-!
# A proved polynomial/trigonometric compiler for the outer kernels

The compiler produces exact rational polynomial coefficients and cosine
and sine term lists. Its equality theorem holds at every real point.
-/

namespace ErdosOverlap
public section

@[expose] noncomputable def outerSineSum : List Numerics.CosineTerm → ℝ → ℝ
  | [], _ => 0
  | a :: rest, t => (a.weight : ℝ)*Real.sin ((a.frequency : ℝ)*t) + outerSineSum rest t

theorem outerSineSum_append (xs ys : List Numerics.CosineTerm) (t : ℝ) :
    outerSineSum (xs ++ ys) t = outerSineSum xs t + outerSineSum ys t := by
  induction xs with
  | nil => simp [outerSineSum]
  | cons x xs ih => simp only [List.cons_append, outerSineSum, ih]; ring

theorem outerCosineSum_append (xs ys : List Numerics.CosineTerm) (t : ℝ) :
    Numerics.cosineSum (xs ++ ys) t = Numerics.cosineSum xs t + Numerics.cosineSum ys t := by
  induction xs with
  | nil => simp [Numerics.cosineSum]
  | cons x xs ih => simp only [List.cons_append, Numerics.cosineSum, ih]; ring

structure OuterFourierPolynomial where
  constant : ℚ
  linear : ℚ
  quadratic : ℚ
  cosineTerms : List Numerics.CosineTerm
  sineTerms : List Numerics.CosineTerm
  deriving Repr

@[expose] def outerTrigTermsEqual (xs : List Numerics.CosineTerm) : List Numerics.CosineTerm → Bool :=
  List.rec (fun ys => ys.isEmpty)
    (fun x _ recurse ys => match ys with
      | [] => false
      | y :: ys => decide (x.frequency = y.frequency) && decide (x.weight = y.weight) && recurse ys) xs

theorem outerTrigTermsEqual_sound (xs ys : List Numerics.CosineTerm)
    (hc : outerTrigTermsEqual xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [outerTrigTermsEqual]
  | cons x xs ih =>
    cases ys with
    | nil => simp [outerTrigTermsEqual] at hc
    | cons y ys =>
      simp only [outerTrigTermsEqual, Bool.and_eq_true, decide_eq_true_eq] at hc
      have heq : x = y := by cases x; cases y; simp_all
      exact congrArg₂ List.cons heq (ih ys hc.2)

@[expose] def OuterFourierPolynomial.same (p q : OuterFourierPolynomial) : Bool :=
  decide (p.constant = q.constant) && decide (p.linear = q.linear) &&
    decide (p.quadratic = q.quadratic) && outerTrigTermsEqual p.cosineTerms q.cosineTerms &&
      outerTrigTermsEqual p.sineTerms q.sineTerms

theorem OuterFourierPolynomial.same_sound {p q : OuterFourierPolynomial}
    (h : p.same q = true) : p = q := by
  simp only [same, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc := outerTrigTermsEqual_sound _ _ h.1.2
  have hs := outerTrigTermsEqual_sound _ _ h.2
  cases p; cases q
  simp_all

@[expose] def OuterFourierPolynomial.add (p q : OuterFourierPolynomial) : OuterFourierPolynomial :=
  ⟨p.constant+q.constant, p.linear+q.linear, p.quadratic+q.quadratic,
    p.cosineTerms++q.cosineTerms, p.sineTerms++q.sineTerms⟩

@[expose] noncomputable def OuterFourierPolynomial.value (p : OuterFourierPolynomial) (t : ℝ) : ℝ :=
  (p.constant : ℝ)+(p.linear : ℝ)*t+(p.quadratic : ℝ)*t^2+
    Numerics.cosineSum p.cosineTerms t+outerSineSum p.sineTerms t

theorem OuterFourierPolynomial.value_add (p q : OuterFourierPolynomial) (t : ℝ) :
    (p.add q).value t = p.value t + q.value t := by
  simp only [add, value, Rat.cast_add, outerCosineSum_append, outerSineSum_append]
  ring

@[expose] def OuterTerm.compile (lo hi : ℚ) (term : OuterTerm) : OuterFourierPolynomial :=
  let c := term.multiplier * term.feature.upper lo hi
  match term.feature with
  | .mean => ⟨c, -term.multiplier, 0, [], []⟩
  | .negativeMean => ⟨c, term.multiplier, 0, [], []⟩
  | .secondMoment => ⟨c, 0, -term.multiplier, [], []⟩
  | .cosine r => ⟨c, 0, 0, [⟨r.frequency, -term.multiplier⟩], []⟩
  | .sine r => ⟨c, 0, 0, [], [⟨r.frequency, -term.multiplier⟩]⟩
  | .negativeSine r => ⟨c, 0, 0, [], [⟨r.frequency, term.multiplier⟩]⟩
  | .mixed r alpha => ⟨c, 0, 0, [⟨r.frequency, -term.multiplier⟩],
      [⟨r.frequency, -term.multiplier*alpha⟩]⟩

theorem OuterTerm.compile_value (lo hi : ℚ) (term : OuterTerm) (t : ℝ) :
    (term.compile lo hi).value t = term.value lo hi t := by
  cases heq : term.feature <;>
    simp only [compile, heq, OuterFourierPolynomial.value, Numerics.cosineSum, Numerics.CosineTerm.value,
      outerSineSum, OuterTerm.value, OuterFeature.value, Rat.cast_mul, Rat.cast_neg,
      Rat.cast_zero] <;> ring

@[expose] def compileOuterCorrection (lo hi : ℚ) : List OuterTerm → OuterFourierPolynomial
  | [] => ⟨0, 0, 0, [], []⟩
  | term :: rest => (term.compile lo hi).add (compileOuterCorrection lo hi rest)

theorem compileOuterCorrection_value (lo hi : ℚ) (terms : List OuterTerm) (t : ℝ) :
    (compileOuterCorrection lo hi terms).value t = outerCorrection lo hi terms t := by
  induction terms with
  | nil => simp [compileOuterCorrection, OuterFourierPolynomial.value,
      Numerics.cosineSum, outerSineSum, outerCorrection]
  | cons term rest ih =>
    rw [compileOuterCorrection, OuterFourierPolynomial.value_add, term.compile_value, ih]
    rfl

@[expose] def OuterBinData.compile (b : OuterBinData) : OuterFourierPolynomial :=
  (⟨1, 0, 0, [], []⟩ : OuterFourierPolynomial).add (compileOuterCorrection b.lo b.hi b.terms)

/-- The rational compiler is an exact identity, independent of any
numerical integration procedure or proposed output table. -/
theorem OuterBinData.compile_value (b : OuterBinData) (t : ℝ) :
    b.compile.value t = b.kernel t := by
  rw [compile, OuterFourierPolynomial.value_add, compileOuterCorrection_value]
  simp [OuterFourierPolynomial.value, Numerics.cosineSum, outerSineSum,
    OuterBinData.kernel, outerKernel]

end
end ErdosOverlap
