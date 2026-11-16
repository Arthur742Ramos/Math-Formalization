module

public import ErdosOverlap.Numerics.FastTrig
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Exact Fourier-polynomial primitives and interval enclosures -/

namespace ErdosOverlap.Numerics

open LeanCert.Core MeasureTheory

public section
noncomputable section

structure CosineTerm where
  frequency : ℚ
  weight : ℚ
  deriving DecidableEq, Repr

@[expose] def CosineTerm.value (a : CosineTerm) (x : ℝ) : ℝ :=
  a.weight * Real.cos (a.frequency * x)

@[expose] def CosineTerm.primitive (a : CosineTerm) (x : ℝ) : ℝ :=
  if a.frequency = 0 then (a.weight : ℝ) * x
  else ((a.weight / a.frequency : ℚ) : ℝ) * Real.sin ((a.frequency : ℝ) * x)

@[expose] def cosineSum : List CosineTerm → ℝ → ℝ
  | [], _ => 0
  | a :: rest, x => a.value x + cosineSum rest x

@[expose] def cosinePrimitive : List CosineTerm → ℝ → ℝ
  | [], _ => 0
  | a :: rest, x => a.primitive x + cosinePrimitive rest x

structure FourierPolynomial where
  constant : ℚ
  linear : ℚ
  quadratic : ℚ
  terms : List CosineTerm
  deriving DecidableEq, Repr

@[expose] def FourierPolynomial.value (p : FourierPolynomial) (x : ℝ) : ℝ :=
  p.constant + p.linear*x + p.quadratic*x^2 + cosineSum p.terms x

@[expose] def FourierPolynomial.primitive (p : FourierPolynomial) (x : ℝ) : ℝ :=
  p.constant*x + p.linear*x^2/2 + p.quadratic*x^3/3 + cosinePrimitive p.terms x

theorem CosineTerm.hasDerivAt_primitive (a : CosineTerm) (x : ℝ) :
    HasDerivAt a.primitive (a.value x) x := by
  change HasDerivAt (fun y : ℝ => if a.frequency = 0 then (a.weight : ℝ)*y
    else ((a.weight / a.frequency : ℚ) : ℝ) * Real.sin ((a.frequency : ℝ)*y))
      ((a.weight : ℝ)*Real.cos ((a.frequency : ℝ)*x)) x
  by_cases hf : a.frequency = 0
  · simp only [hf, ite_true, Rat.cast_zero,
      zero_mul, Real.cos_zero, mul_one]
    convert! (hasDerivAt_id x).const_mul (a.weight : ℝ) using 1 <;> simp
  · have hfr : (a.frequency : ℝ) ≠ 0 := by exact_mod_cast hf
    have hd := ((Real.hasDerivAt_sin ((a.frequency : ℝ)*x)).comp x
      ((hasDerivAt_id x).const_mul (a.frequency : ℝ))).const_mul
        ((a.weight / a.frequency : ℚ) : ℝ)
    simp only [hf, ite_false]
    convert! hd using 1 <;> simp only [Rat.cast_div, mul_one, Function.comp_def]
    field_simp

theorem cosineSum_continuous (terms : List CosineTerm) : Continuous (cosineSum terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons a rest ih =>
    change Continuous (fun x => a.weight * Real.cos (a.frequency*x) + cosineSum rest x)
    exact (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).add ih

theorem cosinePrimitive_hasDerivAt (terms : List CosineTerm) (x : ℝ) :
    HasDerivAt (cosinePrimitive terms) (cosineSum terms x) x := by
  induction terms with
  | nil => exact hasDerivAt_const x 0
  | cons a rest ih => exact (a.hasDerivAt_primitive x).add ih

theorem FourierPolynomial.continuous (p : FourierPolynomial) : Continuous p.value := by
  exact ((continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul (continuous_id.pow 2))).add (cosineSum_continuous p.terms)

theorem FourierPolynomial.hasDerivAt_primitive (p : FourierPolynomial) (x : ℝ) :
    HasDerivAt p.primitive (p.value x) x := by
  have h0 := (hasDerivAt_id x).const_mul (p.constant : ℝ)
  have h1 := ((hasDerivAt_id x).pow 2).const_mul (p.linear : ℝ) |>.div_const 2
  have h2 := ((hasDerivAt_id x).pow 3).const_mul (p.quadratic : ℝ) |>.div_const 3
  have hs := cosinePrimitive_hasDerivAt p.terms x
  convert ((h0.add h1).add h2).add hs using 1
  · rfl
  · dsimp only [FourierPolynomial.value, id_eq]
    ring

theorem FourierPolynomial.integral_eq_primitive (p : FourierPolynomial) (a b : ℝ) :
    (∫ x in a..b, p.value x) = p.primitive b - p.primitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt_primitive x) (p.continuous.intervalIntegrable a b)

end

@[expose] def CosineTerm.enclosure (a : CosineTerm) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  let argument := (rationalDyadic a.frequency precision).mulRounded I precision
  (rationalDyadic a.weight precision).mulRounded (cosDyadicFast argument degree precision) precision

theorem CosineTerm.mem_enclosure (a : CosineTerm) {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    a.value x ∈ a.enclosure I degree precision := by
  have ha := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_mul (mem_rationalDyadic a.frequency precision hp) hx) precision
  exact IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_mul (mem_rationalDyadic a.weight precision hp)
      (mem_cosDyadicFast ha degree precision hp)) precision

@[expose] def cosineEnclosure (I : IntervalDyadic) (degree : ℕ) (precision : ℤ) :
    List CosineTerm → IntervalDyadic
  | [] => rationalDyadic 0 precision
  | a :: rest => (a.enclosure I degree precision).addRounded
      (cosineEnclosure I degree precision rest) precision

theorem mem_cosineEnclosure {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) (terms : List CosineTerm) :
    cosineSum terms x ∈ cosineEnclosure I degree precision terms := by
  induction terms with
  | nil => simpa only [cosineSum, cosineEnclosure, Rat.cast_zero] using
      mem_rationalDyadic 0 precision hp
  | cons a rest ih =>
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add (a.mem_enclosure hx degree precision hp) ih) precision

@[expose] def FourierPolynomial.enclosure (p : FourierPolynomial) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  let quad := (rationalDyadic p.quadratic precision).mulRounded I precision
  let lin := (rationalDyadic p.linear precision).addRounded quad precision
  let poly := (rationalDyadic p.constant precision).addRounded (lin.mulRounded I precision) precision
  poly.addRounded (cosineEnclosure I degree precision p.terms) precision

theorem FourierPolynomial.mem_enclosure (p : FourierPolynomial) {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    p.value x ∈ p.enclosure I degree precision := by
  have hq := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_mul (mem_rationalDyadic p.quadratic precision hp) hx) precision
  have hl := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_add (mem_rationalDyadic p.linear precision hp) hq) precision
  have hm := IntervalDyadic.roundOut_contains (IntervalDyadic.mem_mul hl hx) precision
  have hc := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_add (mem_rationalDyadic p.constant precision hp) hm) precision
  have hs := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_add hc (mem_cosineEnclosure hx degree precision hp p.terms)) precision
  have he : p.value x = (p.constant + (p.linear+p.quadratic*x)*x) + cosineSum p.terms x := by
    dsimp only [FourierPolynomial.value]
    ring
  rw [he]
  exact hs

end
end ErdosOverlap.Numerics
