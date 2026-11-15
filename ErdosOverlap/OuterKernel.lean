/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.SignedKernel

/-!
# A finite physical schema for the 180 outer mean certificates

The seven feature constructors are exactly those occurring in the selected
outer bins. Rational sine bounds are verified through a squared inequality;
no numerical square-root evaluator is part of the trusted argument.
-/

namespace ErdosOverlap
open MeasureTheory Set
public section

structure OuterFrequencyData where
  frequency : ℚ
  cosineBound : ℚ
  sineBound : ℚ
  deriving Repr

@[expose] noncomputable def OuterFrequencyData.Valid (r : OuterFrequencyData) : Prop :=
  Real.sinc (r.frequency : ℝ)^2 ≤ (r.cosineBound : ℝ) ∧
    r.cosineBound ≤ 1/2 ∧ 0 ≤ r.sineBound ∧
    4*r.cosineBound*(1-r.cosineBound) ≤ r.sineBound^2

@[expose] def OuterFrequencyData.rationalChecks (r : OuterFrequencyData) : Bool :=
  decide (r.cosineBound ≤ 1/2 ∧ 0 ≤ r.sineBound ∧
    4*r.cosineBound*(1-r.cosineBound) ≤ r.sineBound^2)

theorem OuterFrequencyData.valid_of_checks (r : OuterFrequencyData)
    (hsinc : Real.sinc (r.frequency : ℝ)^2 ≤ (r.cosineBound : ℝ))
    (hrat : r.rationalChecks = true) : r.Valid :=
  ⟨hsinc, of_decide_eq_true hrat⟩

theorem sine_pairing_le_of_square_bounds {h : ℝ → ℝ} (hh : Admissible h)
    (ξ C S : ℝ) (hC : Real.sinc ξ^2 ≤ C) (hhalf : C ≤ 1/2)
    (hS : 0 ≤ S) (hSS : 4*C*(1-C) ≤ S^2) :
    |squarePairing h (fun t => Real.sin (ξ*t))| ≤ S := by
  have hc := contrast_norm_sq_le hh ξ
  have hraw : contrastSin h ξ^2 ≤ 4*(1-Real.sinc ξ^2) := by
    nlinarith [sq_nonneg (contrastCos h ξ)]
  have hmul := mul_le_mul_of_nonneg_left hraw (sq_nonneg (Real.sinc ξ))
  have hmono : 4*(Real.sinc ξ^2)*(1-Real.sinc ξ^2) ≤ 4*C*(1-C) := by
    have hp := mul_nonneg (sub_nonneg.mpr hC)
      (show 0 ≤ 1-C-Real.sinc ξ^2 by linarith)
    nlinarith
  have hsq : squarePairing h (fun t => Real.sin (ξ*t))^2 ≤ S^2 := by
    rw [squarePairing_sin_identity hh ξ]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) hS).mp (by simpa only [sq_abs] using hsq)

theorem OuterFrequencyData.sine_bound {h : ℝ → ℝ} (hh : Admissible h)
    (r : OuterFrequencyData) (hv : r.Valid) :
    |squarePairing h (fun t => Real.sin ((r.frequency : ℝ)*t))| ≤ (r.sineBound : ℝ) := by
  apply sine_pairing_le_of_square_bounds hh _ _ _ hv.1
  · have hc : (r.cosineBound : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast hv.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  · exact_mod_cast hv.2.2.1
  · exact_mod_cast hv.2.2.2

inductive OuterFeature where
  | mean
  | negativeMean
  | secondMoment
  | cosine (frequency : OuterFrequencyData)
  | sine (frequency : OuterFrequencyData)
  | negativeSine (frequency : OuterFrequencyData)
  | mixed (frequency : OuterFrequencyData) (alpha : ℚ)
  deriving Repr

@[expose] noncomputable def OuterFeature.value : OuterFeature → ℝ → ℝ
  | .mean, t => t
  | .negativeMean, t => -t
  | .secondMoment, t => t^2
  | .cosine r, t => Real.cos ((r.frequency : ℝ)*t)
  | .sine r, t => Real.sin ((r.frequency : ℝ)*t)
  | .negativeSine r, t => -Real.sin ((r.frequency : ℝ)*t)
  | .mixed r alpha, t => Real.cos ((r.frequency : ℝ)*t) +
      (alpha : ℝ)*Real.sin ((r.frequency : ℝ)*t)

@[expose] def OuterFeature.upper (lo hi : ℚ) : OuterFeature → ℚ
  | .mean => hi
  | .negativeMean => -lo
  | .secondMoment => 2/3 + max (lo^2) (hi^2)/2
  | .cosine r => r.cosineBound
  | .sine r => r.sineBound
  | .negativeSine r => r.sineBound
  | .mixed r alpha => (1+alpha^2)*r.cosineBound

@[expose] noncomputable def OuterFeature.Valid : OuterFeature → Prop
  | .mean | .negativeMean | .secondMoment => True
  | .cosine r | .sine r | .negativeSine r | .mixed r _ => r.Valid

theorem OuterFeature.continuous (feature : OuterFeature) : Continuous feature.value := by
  change Continuous (fun t => feature.value t)
  cases feature <;> simp only [OuterFeature.value]
  · exact continuous_id
  · exact continuous_id.neg
  · exact continuous_id.pow 2
  · exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
  · exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).neg
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).add
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))

theorem sq_le_max_endpoints {lo hi m : ℝ} (hm : m ∈ Icc lo hi) : m^2 ≤ max (lo^2) (hi^2) := by
  by_cases h : 0 ≤ m
  · apply le_trans _ (le_max_right _ _)
    have hh : 0 ≤ hi := h.trans hm.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) (add_nonneg hh h)]
  · apply le_trans _ (le_max_left _ _)
    have hm0 : m ≤ 0 := le_of_not_ge h
    have hl : lo ≤ 0 := hm.1.trans hm0
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.1) (show 0 ≤ -lo-m by linarith)]

theorem OuterFeature.upper_bound {h : ℝ → ℝ} (hh : Admissible h)
    {lo hi : ℚ} (hm : profileMean (overlapProfile h) ∈ Icc (lo : ℝ) (hi : ℝ))
    (feature : OuterFeature) (hv : feature.Valid) :
    squarePairing h feature.value ≤ (feature.upper lo hi : ℝ) := by
  cases feature with
  | mean =>
    change squarePairing h (fun t => t) ≤ (hi : ℝ)
    rw [squarePairing_id_eq_mean hh]
    exact hm.2
  | negativeMean =>
    have heq : (OuterFeature.negativeMean).value = (fun t : ℝ => (-1)*t) := by funext t; simp [value]
    rw [heq, squarePairing_mul (Q := fun t : ℝ => t) hh continuous_id, squarePairing_id_eq_mean hh]
    simp only [upper, Rat.cast_neg]
    linarith [hm.1]
  | secondMoment =>
    rw [show OuterFeature.secondMoment.value = (fun t : ℝ => t^2) from rfl,
      squarePairing_sq_eq_mean hh]
    have hb := sq_le_max_endpoints hm
    simpa only [upper, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_max, Rat.cast_pow]
      using (show 2/3+profileMean (overlapProfile h)^2/2 ≤
        2/3+max ((lo : ℝ)^2) ((hi : ℝ)^2)/2 by linarith)
  | cosine r => exact (squarePairing_cos_le_sinc_sq hh (r.frequency : ℝ)).trans hv.1
  | sine r => exact (abs_le.mp (r.sine_bound hh hv)).2
  | negativeSine r =>
    have heq : (OuterFeature.negativeSine r).value =
        (fun t : ℝ => (-1)*Real.sin ((r.frequency : ℝ)*t)) := by funext t; simp [value]
    rw [heq, squarePairing_mul (Q := fun t => Real.sin ((r.frequency : ℝ)*t)) hh
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))]
    have hb := (abs_le.mp (r.sine_bound hh hv)).1
    change (-1)*squarePairing h (fun t => Real.sin ((r.frequency : ℝ)*t)) ≤ (r.sineBound : ℝ)
    linarith
  | mixed r alpha =>
    have h₁ := squarePairing_cos_add_mul_sin_bound hh (r.frequency : ℝ) (alpha : ℝ)
    have h₂ := mul_le_mul_of_nonneg_left hv.1 (show 0 ≤ 1+(alpha : ℝ)^2 by positivity)
    change squarePairing h (fun t => Real.cos ((r.frequency : ℝ)*t) +
      (alpha : ℝ)*Real.sin ((r.frequency : ℝ)*t)) ≤ _
    rw [squarePairing_add (Q := fun t => Real.cos ((r.frequency : ℝ)*t))
      (J := fun t => (alpha : ℝ)*Real.sin ((r.frequency : ℝ)*t)) hh
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))),
      squarePairing_mul (Q := fun t => Real.sin ((r.frequency : ℝ)*t)) hh
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))]
    simpa only [upper, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_pow] using h₁.trans h₂

structure OuterTerm where
  feature : OuterFeature
  multiplier : ℚ
  deriving Repr

@[expose] noncomputable def OuterTerm.value (lo hi : ℚ) (term : OuterTerm) (t : ℝ) : ℝ :=
  (term.multiplier : ℝ) * ((term.feature.upper lo hi : ℝ) - term.feature.value t)

@[expose] noncomputable def outerCorrection (lo hi : ℚ) : List OuterTerm → ℝ → ℝ
  | [], _ => 0
  | term :: rest, t => term.value lo hi t + outerCorrection lo hi rest t

@[expose] noncomputable def outerKernel (lo hi : ℚ) (terms : List OuterTerm) (t : ℝ) : ℝ :=
  1 + outerCorrection lo hi terms t

theorem OuterTerm.continuous (lo hi : ℚ) (term : OuterTerm) : Continuous (term.value lo hi) :=
  continuous_const.mul (continuous_const.sub term.feature.continuous)

theorem outerCorrection_continuous (lo hi : ℚ) (terms : List OuterTerm) :
    Continuous (outerCorrection lo hi terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons term rest ih => exact (term.continuous lo hi).add ih

theorem outerKernel_continuous (lo hi : ℚ) (terms : List OuterTerm) :
    Continuous (outerKernel lo hi terms) :=
  continuous_const.add (outerCorrection_continuous lo hi terms)

theorem outerCorrection_nonnegative {h : ℝ → ℝ} (hh : Admissible h) {lo hi : ℚ}
    (hm : profileMean (overlapProfile h) ∈ Icc (lo : ℝ) (hi : ℝ))
    (terms : List OuterTerm)
    (hv : ∀ term ∈ terms, 0 ≤ term.multiplier ∧ term.feature.Valid) :
    0 ≤ squarePairing h (outerCorrection lo hi terms) := by
  induction terms with
  | nil => simp [outerCorrection, squarePairing_const hh]
  | cons term rest ih =>
    change 0 ≤ squarePairing h (fun t => term.value lo hi t + outerCorrection lo hi rest t)
    rw [squarePairing_add hh (term.continuous lo hi) (outerCorrection_continuous lo hi rest)]
    apply add_nonneg _ (ih (fun r hr => hv r (List.mem_cons_of_mem term hr)))
    have hvalid := hv term List.mem_cons_self
    change 0 ≤ squarePairing h (fun t => (term.multiplier : ℝ) *
      ((term.feature.upper lo hi : ℝ) - term.feature.value t))
    rw [squarePairing_mul (Q := fun t => (term.feature.upper lo hi : ℝ) - term.feature.value t)
      hh (continuous_const.sub term.feature.continuous),
      squarePairing_sub (Q := fun _ => (term.feature.upper lo hi : ℝ)) (J := term.feature.value)
      hh continuous_const term.feature.continuous, squarePairing_const hh]
    exact mul_nonneg (by exact_mod_cast hvalid.1)
      (sub_nonneg.mpr (term.feature.upper_bound hh hm hvalid.2))

/-- The outer kernel has expectation at least one for every actual
partition whose mean belongs to the certified interval. -/
theorem outerKernel_expectation {h : ℝ → ℝ} (hh : Admissible h) {lo hi : ℚ}
    (hm : profileMean (overlapProfile h) ∈ Icc (lo : ℝ) (hi : ℝ))
    (terms : List OuterTerm)
    (hv : ∀ term ∈ terms, 0 ≤ term.multiplier ∧ term.feature.Valid) :
    1 ≤ squarePairing h (outerKernel lo hi terms) := by
  change 1 ≤ squarePairing h (fun t => 1 + outerCorrection lo hi terms t)
  rw [squarePairing_add hh continuous_const (outerCorrection_continuous lo hi terms),
    squarePairing_const hh]
  linarith [outerCorrection_nonnegative hh hm terms hv]

theorem outerKernel_cap_bound {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h)
    (hcap : OverlapCap h M) {lo hi : ℚ}
    (hm : profileMean (overlapProfile h) ∈ Icc (lo : ℝ) (hi : ℝ))
    (terms : List OuterTerm)
    (hv : ∀ term ∈ terms, 0 ≤ term.multiplier ∧ term.feature.Valid) :
    1 ≤ M * signedKernelDenominator (outerKernel lo hi terms) :=
  (outerKernel_expectation hh hm terms hv).trans
    (squarePairing_le_cap hh hcap (outerKernel_continuous lo hi terms))

end
end ErdosOverlap
