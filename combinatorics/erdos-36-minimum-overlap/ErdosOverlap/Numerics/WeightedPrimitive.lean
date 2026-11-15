module

public import ErdosOverlap.Numerics.FourierPolynomial
public import ErdosOverlap.Numerics.FastTrig

/-! # Exact first-moment primitives for Fourier-polynomial cells -/

namespace ErdosOverlap.Numerics

open MeasureTheory LeanCert.Core

public section
noncomputable section

@[expose] def CosineTerm.weightedPrimitive (a : CosineTerm) (x : ℝ) : ℝ :=
  if a.frequency = 0 then (a.weight : ℝ)*x^2/2
  else ((a.weight/a.frequency : ℚ) : ℝ)*x*Real.sin ((a.frequency : ℝ)*x) +
    ((a.weight/a.frequency^2 : ℚ) : ℝ)*Real.cos ((a.frequency : ℝ)*x)

@[expose] def cosineWeightedPrimitive : List CosineTerm → ℝ → ℝ
  | [], _ => 0
  | a :: rest, x => a.weightedPrimitive x + cosineWeightedPrimitive rest x

@[expose] def FourierPolynomial.weightedPrimitive (p : FourierPolynomial) (x : ℝ) : ℝ :=
  p.constant*x^2/2 + p.linear*x^3/3 + p.quadratic*x^4/4 +
    cosineWeightedPrimitive p.terms x

theorem CosineTerm.hasDerivAt_weightedPrimitive (a : CosineTerm) (x : ℝ) :
    HasDerivAt a.weightedPrimitive (x*a.value x) x := by
  change HasDerivAt (fun y : ℝ => if a.frequency = 0 then (a.weight : ℝ)*y^2/2
    else ((a.weight/a.frequency : ℚ) : ℝ)*y*Real.sin ((a.frequency : ℝ)*y) +
      ((a.weight/a.frequency^2 : ℚ) : ℝ)*Real.cos ((a.frequency : ℝ)*y)) _ x
  by_cases hf : a.frequency = 0
  · simp only [hf, ite_true]
    have hd := (((hasDerivAt_id x).pow 2).const_mul (a.weight : ℝ)).div_const 2
    convert! hd using 1
    dsimp only [CosineTerm.value, id_eq, Function.comp_def]
    rw [hf]
    simp only [Rat.cast_zero, zero_mul, Real.cos_zero]
    ring
  · have hfr : (a.frequency : ℝ) ≠ 0 := by exact_mod_cast hf
    simp only [hf, ite_false]
    have hx := (hasDerivAt_id x).const_mul (a.frequency : ℝ)
    have hs := (Real.hasDerivAt_sin ((a.frequency : ℝ)*x)).comp x hx
    have hc := (Real.hasDerivAt_cos ((a.frequency : ℝ)*x)).comp x hx
    have h1 := ((hasDerivAt_id x).const_mul ((a.weight/a.frequency : ℚ) : ℝ)).mul hs
    have h2 := hc.const_mul ((a.weight/a.frequency^2 : ℚ) : ℝ)
    convert! h1.add h2 using 1
    dsimp only [CosineTerm.value, id_eq, Function.comp_def]
    simp only [Rat.cast_div, Rat.cast_pow, mul_one]
    field_simp
    ring

theorem cosineWeightedPrimitive_hasDerivAt (terms : List CosineTerm) (x : ℝ) :
    HasDerivAt (cosineWeightedPrimitive terms) (x*cosineSum terms x) x := by
  induction terms with
  | nil =>
    convert! hasDerivAt_const x (0 : ℝ) using 1
    simp only [cosineSum, mul_zero]
  | cons a rest ih =>
    have hd := (a.hasDerivAt_weightedPrimitive x).add ih
    convert! hd using 1
    dsimp only [cosineSum]
    ring

theorem FourierPolynomial.hasDerivAt_weightedPrimitive (p : FourierPolynomial) (x : ℝ) :
    HasDerivAt p.weightedPrimitive (x*p.value x) x := by
  have h0 := (((hasDerivAt_id x).pow 2).const_mul (p.constant : ℝ)).div_const 2
  have h1 := (((hasDerivAt_id x).pow 3).const_mul (p.linear : ℝ)).div_const 3
  have h2 := (((hasDerivAt_id x).pow 4).const_mul (p.quadratic : ℝ)).div_const 4
  have hs := cosineWeightedPrimitive_hasDerivAt p.terms x
  convert! ((h0.add h1).add h2).add hs using 1
  dsimp only [FourierPolynomial.value, id_eq]
  ring

theorem FourierPolynomial.integral_weighted_eq_primitive (p : FourierPolynomial) (a b : ℝ) :
    (∫ x in a..b, x*p.value x) = p.weightedPrimitive b-p.weightedPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt_weightedPrimitive x)
      ((continuous_id.mul p.continuous).intervalIntegrable a b)

theorem FourierPolynomial.integral_affine_weight_eq (p : FourierPolynomial)
    (a b α β : ℝ) :
    (∫ x in a..b, (α+β*x)*p.value x) =
      α*(p.primitive b-p.primitive a) +
      β*(p.weightedPrimitive b-p.weightedPrimitive a) := by
  have hf : IntervalIntegrable p.value volume a b := p.continuous.intervalIntegrable a b
  have hxf : IntervalIntegrable (fun x => x*p.value x) volume a b :=
    (continuous_id.mul p.continuous).intervalIntegrable a b
  calc
    _ = ∫ x in a..b, α*p.value x+β*(x*p.value x) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = α*(∫ x in a..b, p.value x)+β*(∫ x in a..b, x*p.value x) := by
      rw [intervalIntegral.integral_add (hf.const_mul α) (hxf.const_mul β),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = _ := by rw [p.integral_eq_primitive, p.integral_weighted_eq_primitive]

end
end
end ErdosOverlap.Numerics
