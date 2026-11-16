/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.OuterApproximation

/-! # Shared trigonometric polynomial approximations and exact weighted assembly -/

namespace ErdosOverlap.Numerics
open MeasureTheory Set
@[expose] public section

def outerAddPolynomialCoefficients : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: outerAddPolynomialCoefficients xs ys

def scalePolynomialCoefficients (w : ℚ) (cs : List ℚ) : List ℚ := cs.map (w * ·)

theorem polynomialValue_addCoefficients (xs ys : List ℚ) (u : ℝ) :
    polynomialValue (outerAddPolynomialCoefficients xs ys) u =
      polynomialValue xs u + polynomialValue ys u := by
  induction xs generalizing ys with
  | nil => simp [outerAddPolynomialCoefficients, polynomialValue]
  | cons x xs ih =>
    cases ys with
    | nil => simp [outerAddPolynomialCoefficients, polynomialValue]
    | cons y ys => simp only [outerAddPolynomialCoefficients, polynomialValue, Rat.cast_add, ih]; ring

theorem polynomialValue_scaleCoefficients (w : ℚ) (cs : List ℚ) (u : ℝ) :
    polynomialValue (scalePolynomialCoefficients w cs) u = (w : ℝ)*polynomialValue cs u := by
  induction cs with
  | nil => simp [scalePolynomialCoefficients, polynomialValue]
  | cons c cs ih =>
    simp only [scalePolynomialCoefficients, List.map_cons, polynomialValue, Rat.cast_mul] at *
    rw [ih]
    ring

structure LocalTrigApprox where
  frequency : ℚ
  cosineCoefficients : List ℚ
  sineCoefficients : List ℚ
  error : ℚ
  deriving Repr

noncomputable def LocalTrigApprox.Correct (a : LocalTrigApprox) (center radius : ℚ) : Prop :=
  ∀ u : ℝ, |u| ≤ 1 →
    |Real.cos ((a.frequency : ℝ)*((center : ℝ)+(radius : ℝ)*u))-
      polynomialValue a.cosineCoefficients u| ≤ (a.error : ℝ) ∧
    |Real.sin ((a.frequency : ℝ)*((center : ℝ)+(radius : ℝ)*u))-
      polynomialValue a.sineCoefficients u| ≤ (a.error : ℝ)

def LocalTrigApprox.check (a : LocalTrigApprox) (seeds : List TrigSeed)
    (radius ε : ℚ) : Bool :=
  (⟨0,0,0,[⟨a.frequency,1⟩],[]⟩ : OuterFourierPolynomial).approximationCheck
    seeds radius a.cosineCoefficients ε a.error &&
  (⟨0,0,0,[],[⟨a.frequency,1⟩]⟩ : OuterFourierPolynomial).approximationCheck
    seeds radius a.sineCoefficients ε a.error

theorem LocalTrigApprox.check_sound {a : LocalTrigApprox} {seeds : List TrigSeed}
    {center radius ε : ℚ} (hs : ∀ s ∈ seeds, s.Correct center)
    (hc : a.check seeds radius ε = true) : a.Correct center radius := by
  simp only [check, Bool.and_eq_true] at hc
  intro u hu
  have hcos := OuterFourierPolynomial.approximationCheck_sound _ hs hc.1 hu
  have hsin := OuterFourierPolynomial.approximationCheck_sound _ hs hc.2 hu
  simpa only [OuterFourierPolynomial.trigValue, cosineSum, CosineTerm.value,
    outerSineSum, Rat.cast_one, one_mul, zero_add, add_zero] using And.intro hcos hsin

def localTrigLookup (frequency : ℚ) : List LocalTrigApprox → LocalTrigApprox
  | [] => ⟨frequency, [], [], 1⟩
  | a :: as => if frequency = a.frequency then a else localTrigLookup frequency as

theorem localTrigLookup_frequency (frequency : ℚ) (basis : List LocalTrigApprox) :
    (localTrigLookup frequency basis).frequency = frequency := by
  induction basis with
  | nil => rfl
  | cons a as ih =>
    unfold localTrigLookup
    split_ifs with he
    · exact he.symm
    · exact ih

theorem localTrigLookup_correct {basis : List LocalTrigApprox} {center radius : ℚ}
    (hb : ∀ a ∈ basis, a.Correct center radius) (frequency : ℚ) :
    (localTrigLookup frequency basis).Correct center radius := by
  induction basis with
  | nil =>
    intro u _
    simp only [localTrigLookup, polynomialValue, sub_zero, Rat.cast_one]
    exact ⟨Real.abs_cos_le_one _, Real.abs_sin_le_one _⟩
  | cons a as ih =>
    unfold localTrigLookup
    split_ifs
    · exact hb a (by simp)
    · exact ih (fun b hb' => hb b (by simp [hb']))

def compileTrigCoefficients (sine : Bool) (basis : List LocalTrigApprox) :
    List CosineTerm → List ℚ
  | [] => []
  | a :: as =>
    let b := localTrigLookup a.frequency basis
    outerAddPolynomialCoefficients
      (scalePolynomialCoefficients a.weight (if sine then b.sineCoefficients else b.cosineCoefficients))
      (compileTrigCoefficients sine basis as)

def compiledTrigError (basis : List LocalTrigApprox) : List CosineTerm → ℚ
  | [] => 0
  | a :: as => |a.weight| *(localTrigLookup a.frequency basis).error+compiledTrigError basis as

theorem compiledCosine_error (terms : List CosineTerm) {basis : List LocalTrigApprox}
    {center radius : ℚ} (hb : ∀ a ∈ basis, a.Correct center radius) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum terms ((center : ℝ)+(radius : ℝ)*u)-
      polynomialValue (compileTrigCoefficients false basis terms) u| ≤
      (compiledTrigError basis terms : ℝ) := by
  induction terms with
  | nil => simp [cosineSum, compileTrigCoefficients, polynomialValue, compiledTrigError]
  | cons a as ih =>
    have ha := (localTrigLookup_correct hb a.frequency u hu).1
    rw [localTrigLookup_frequency] at ha
    have hw := mul_le_mul_of_nonneg_left ha (abs_nonneg (a.weight : ℝ))
    have he : cosineSum (a :: as) ((center : ℝ)+(radius : ℝ)*u)-
        polynomialValue (compileTrigCoefficients false basis (a :: as)) u =
        (a.weight : ℝ)*(Real.cos ((a.frequency : ℝ)*((center : ℝ)+(radius : ℝ)*u))-
          polynomialValue (localTrigLookup a.frequency basis).cosineCoefficients u) +
        (cosineSum as ((center : ℝ)+(radius : ℝ)*u)-
          polynomialValue (compileTrigCoefficients false basis as) u) := by
      simp only [cosineSum, CosineTerm.value, compileTrigCoefficients, Bool.false_eq_true,
        ite_false, polynomialValue_addCoefficients, polynomialValue_scaleCoefficients]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    simpa only [compiledTrigError, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, abs_mul] using
      add_le_add hw ih

theorem compiledSine_error (terms : List CosineTerm) {basis : List LocalTrigApprox}
    {center radius : ℚ} (hb : ∀ a ∈ basis, a.Correct center radius) {u : ℝ} (hu : |u| ≤ 1) :
    |outerSineSum terms ((center : ℝ)+(radius : ℝ)*u)-
      polynomialValue (compileTrigCoefficients true basis terms) u| ≤
      (compiledTrigError basis terms : ℝ) := by
  induction terms with
  | nil => simp [outerSineSum, compileTrigCoefficients, polynomialValue, compiledTrigError]
  | cons a as ih =>
    have ha := (localTrigLookup_correct hb a.frequency u hu).2
    rw [localTrigLookup_frequency] at ha
    have hw := mul_le_mul_of_nonneg_left ha (abs_nonneg (a.weight : ℝ))
    have he : outerSineSum (a :: as) ((center : ℝ)+(radius : ℝ)*u)-
        polynomialValue (compileTrigCoefficients true basis (a :: as)) u =
        (a.weight : ℝ)*(Real.sin ((a.frequency : ℝ)*((center : ℝ)+(radius : ℝ)*u))-
          polynomialValue (localTrigLookup a.frequency basis).sineCoefficients u) +
        (outerSineSum as ((center : ℝ)+(radius : ℝ)*u)-
          polynomialValue (compileTrigCoefficients true basis as) u) := by
      simp only [outerSineSum, compileTrigCoefficients, ite_true,
        polynomialValue_addCoefficients, polynomialValue_scaleCoefficients]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    simpa only [compiledTrigError, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, abs_mul] using
      add_le_add hw ih

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.OuterFourierPolynomial
open Numerics
@[expose] public section

def compiledCoefficients (p : OuterFourierPolynomial) (basis : List LocalTrigApprox) : List ℚ :=
  outerAddPolynomialCoefficients (compileTrigCoefficients false basis p.cosineTerms)
    (compileTrigCoefficients true basis p.sineTerms)

def compiledError (p : OuterFourierPolynomial) (basis : List LocalTrigApprox) : ℚ :=
  compiledTrigError basis p.cosineTerms+compiledTrigError basis p.sineTerms

theorem compiled_error (p : OuterFourierPolynomial) {basis : List LocalTrigApprox}
    {center radius : ℚ} (hb : ∀ a ∈ basis, a.Correct center radius) {u : ℝ} (hu : |u| ≤ 1) :
    |p.trigValue ((center : ℝ)+(radius : ℝ)*u)-
      polynomialValue (p.compiledCoefficients basis) u| ≤ (p.compiledError basis : ℝ) := by
  have hc := compiledCosine_error p.cosineTerms hb hu
  have hs := compiledSine_error p.sineTerms hb hu
  have he : p.trigValue ((center : ℝ)+(radius : ℝ)*u)-
      polynomialValue (p.compiledCoefficients basis) u =
      (cosineSum p.cosineTerms ((center : ℝ)+(radius : ℝ)*u)-
        polynomialValue (compileTrigCoefficients false basis p.cosineTerms) u)+
      (outerSineSum p.sineTerms ((center : ℝ)+(radius : ℝ)*u)-
        polynomialValue (compileTrigCoefficients true basis p.sineTerms) u) := by
    simp only [trigValue, compiledCoefficients, polynomialValue_addCoefficients]
    ring
  rw [he]
  simpa only [compiledError, Rat.cast_add] using
    (abs_add_le _ _).trans (add_le_add hc hs)

theorem compiled_value_error (p : OuterFourierPolynomial) {basis : List LocalTrigApprox}
    {center radius : ℚ} (hb : ∀ a ∈ basis, a.Correct center radius)
    (hr : radius ≠ 0) {t : ℝ} (ht : |(t-(center : ℝ))/(radius : ℝ)| ≤ 1) :
    |p.value t-(p.approximation (p.compiledCoefficients basis) center radius).value t| ≤
      (p.compiledError basis : ℝ) := by
  have h := p.compiled_error hb ht
  have hr' : (radius : ℝ) ≠ 0 := by exact_mod_cast hr
  have he : (center : ℝ)+(radius : ℝ)*((t-(center : ℝ))/(radius : ℝ)) = t := by
    field_simp
    ring
  rw [he] at h
  rw [approximation, quadraticPatch_value _ center radius p.constant p.linear p.quadratic hr]
  convert! h using 1
  congr 1
  unfold value trigValue
  ring

end
end ErdosOverlap.OuterFourierPolynomial
