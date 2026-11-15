module

public import ErdosOverlap.Numerics.WeightedPrimitive

/-! # Certified numerical enclosures for exact primitives -/

namespace ErdosOverlap.Numerics

open LeanCert.Core MeasureTheory

@[expose] public section

def CosineTerm.primitiveEnclosure (a : CosineTerm) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  if a.frequency = 0 then (rationalDyadic a.weight precision).mulRounded I precision
  else
    let argument := (rationalDyadic a.frequency precision).mulRounded I precision
    (rationalDyadic (a.weight/a.frequency) precision).mulRounded
      (sinDyadicFast argument degree precision) precision

theorem CosineTerm.mem_primitiveEnclosure (a : CosineTerm) {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    a.primitive x ∈ a.primitiveEnclosure I degree precision := by
  unfold CosineTerm.primitiveEnclosure CosineTerm.primitive
  split_ifs with hf
  · exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_mul (mem_rationalDyadic a.weight precision hp) hx) precision
  · exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_mul (mem_rationalDyadic (a.weight/a.frequency) precision hp)
        (mem_sinDyadicFast (IntervalDyadic.roundOut_contains
          (IntervalDyadic.mem_mul (mem_rationalDyadic a.frequency precision hp) hx) precision)
          degree precision hp)) precision

def CosineTerm.weightedPrimitiveEnclosure (a : CosineTerm) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  if a.frequency = 0 then
    (rationalDyadic (a.weight/2) precision).mulRounded (I.mulRounded I precision) precision
  else
    let argument := (rationalDyadic a.frequency precision).mulRounded I precision
    (I.mulRounded (a.primitiveEnclosure I degree precision) precision).addRounded
      ((rationalDyadic (a.weight/a.frequency^2) precision).mulRounded
        (cosDyadicFast argument degree precision) precision) precision

theorem CosineTerm.mem_weightedPrimitiveEnclosure (a : CosineTerm)
    {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    a.weightedPrimitive x ∈ a.weightedPrimitiveEnclosure I degree precision := by
  unfold CosineTerm.weightedPrimitiveEnclosure CosineTerm.weightedPrimitive
  split_ifs with hf
  · have hm := IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_mul (mem_rationalDyadic (a.weight/2) precision hp)
        (IntervalDyadic.roundOut_contains (IntervalDyadic.mem_mul hx hx) precision)) precision
    convert! hm using 1
    push_cast
    ring
  · have h1 := IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_mul hx (a.mem_primitiveEnclosure hx degree precision hp)) precision
    have h2 := IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_mul (mem_rationalDyadic (a.weight/a.frequency^2) precision hp)
        (mem_cosDyadicFast (IntervalDyadic.roundOut_contains
          (IntervalDyadic.mem_mul (mem_rationalDyadic a.frequency precision hp) hx) precision)
          degree precision hp)) precision
    have hs := IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add h1 h2) precision
    convert! hs using 1
    simp only [CosineTerm.primitive, hf, ite_false]
    ring

def cosinePrimitiveEnclosure (I : IntervalDyadic) (degree : ℕ) (precision : ℤ) :
    List CosineTerm → IntervalDyadic
  | [] => rationalDyadic 0 precision
  | a :: rest => (a.primitiveEnclosure I degree precision).addRounded
      (cosinePrimitiveEnclosure I degree precision rest) precision

def cosineWeightedPrimitiveEnclosure (I : IntervalDyadic) (degree : ℕ) (precision : ℤ) :
    List CosineTerm → IntervalDyadic
  | [] => rationalDyadic 0 precision
  | a :: rest => (a.weightedPrimitiveEnclosure I degree precision).addRounded
      (cosineWeightedPrimitiveEnclosure I degree precision rest) precision

theorem mem_cosinePrimitiveEnclosure {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) (terms : List CosineTerm) :
    cosinePrimitive terms x ∈ cosinePrimitiveEnclosure I degree precision terms := by
  induction terms with
  | nil => simpa only [cosinePrimitive, cosinePrimitiveEnclosure, Rat.cast_zero] using
      mem_rationalDyadic 0 precision hp
  | cons a rest ih =>
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add (a.mem_primitiveEnclosure hx degree precision hp) ih) precision

theorem mem_cosineWeightedPrimitiveEnclosure {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) (terms : List CosineTerm) :
    cosineWeightedPrimitive terms x ∈ cosineWeightedPrimitiveEnclosure I degree precision terms := by
  induction terms with
  | nil => simpa only [cosineWeightedPrimitive, cosineWeightedPrimitiveEnclosure, Rat.cast_zero] using
      mem_rationalDyadic 0 precision hp
  | cons a rest ih =>
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add (a.mem_weightedPrimitiveEnclosure hx degree precision hp) ih) precision

def FourierPolynomial.primitiveEnclosure (p : FourierPolynomial) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  (hornerDyadic I precision [0, p.constant, p.linear/2, p.quadratic/3]).addRounded
    (cosinePrimitiveEnclosure I degree precision p.terms) precision

def FourierPolynomial.weightedPrimitiveEnclosure (p : FourierPolynomial) (I : IntervalDyadic)
    (degree : ℕ) (precision : ℤ) : IntervalDyadic :=
  (hornerDyadic I precision [0, 0, p.constant/2, p.linear/3, p.quadratic/4]).addRounded
    (cosineWeightedPrimitiveEnclosure I degree precision p.terms) precision

theorem FourierPolynomial.mem_primitiveEnclosure (p : FourierPolynomial)
    {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    p.primitive x ∈ p.primitiveEnclosure I degree precision := by
  have hm := mem_hornerDyadic hx precision hp [0, p.constant, p.linear/2, p.quadratic/3]
  have hs := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_add hm (mem_cosinePrimitiveEnclosure hx degree precision hp p.terms)) precision
  convert! hs using 1
  simp [FourierPolynomial.primitive, IntervalRat.hornerVal, Rat.cast_div]
  ring

theorem FourierPolynomial.mem_weightedPrimitiveEnclosure (p : FourierPolynomial)
    {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    p.weightedPrimitive x ∈ p.weightedPrimitiveEnclosure I degree precision := by
  have hm := mem_hornerDyadic hx precision hp [0, 0, p.constant/2, p.linear/3, p.quadratic/4]
  have hs := IntervalDyadic.roundOut_contains
    (IntervalDyadic.mem_add hm
      (mem_cosineWeightedPrimitiveEnclosure hx degree precision hp p.terms)) precision
  convert! hs using 1
  simp [FourierPolynomial.weightedPrimitive, IntervalRat.hornerVal, Rat.cast_div]
  ring

end
end ErdosOverlap.Numerics
