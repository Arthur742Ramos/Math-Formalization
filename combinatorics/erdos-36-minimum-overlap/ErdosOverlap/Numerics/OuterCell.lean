/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.OuterBasis
public import ErdosOverlap.Numerics.OuterPositiveIntegral

/-! # Continuous-cell certificates for the signed outer kernels -/

namespace ErdosOverlap
open Numerics MeasureTheory Set
@[expose] public section

theorem outerSineSum_continuous (terms : List CosineTerm) : Continuous (outerSineSum terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons a as ih =>
    exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).add ih

theorem OuterFourierPolynomial.continuous (p : OuterFourierPolynomial) : Continuous p.value :=
  (((continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul (continuous_id.pow 2))).add
    (cosineSum_continuous p.cosineTerms)).add (outerSineSum_continuous p.sineTerms)

def OuterFourierPolynomial.reflect (p : OuterFourierPolynomial) : OuterFourierPolynomial :=
  ⟨p.constant, -p.linear, p.quadratic, p.cosineTerms,
    p.sineTerms.map (fun a => ⟨a.frequency, -a.weight⟩)⟩

theorem outerCosineSum_neg (terms : List CosineTerm) (t : ℝ) :
    cosineSum terms (-t) = cosineSum terms t := by
  induction terms with
  | nil => rfl
  | cons a as ih => simp only [cosineSum, CosineTerm.value, mul_neg, Real.cos_neg, ih]

theorem outerSineSum_reflect (terms : List CosineTerm) (t : ℝ) :
    outerSineSum (terms.map (fun a => ⟨a.frequency, -a.weight⟩)) t = outerSineSum terms (-t) := by
  induction terms with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, outerSineSum, Rat.cast_neg, mul_neg, Real.sin_neg, ih]
    ring

theorem OuterFourierPolynomial.reflect_value (p : OuterFourierPolynomial) (t : ℝ) :
    p.reflect.value t = p.value (-t) := by
  simp only [reflect, value, Rat.cast_neg, outerSineSum_reflect, outerCosineSum_neg]
  ring

structure OuterCellModel where
  center : ℚ
  radius : ℚ
  coefficients : List ℚ
  error : ℚ
  deriving Repr

def OuterCellModel.polynomial (m : OuterCellModel) (p : OuterFourierPolynomial) : PolynomialPiece :=
  p.approximation m.coefficients m.center m.radius

noncomputable def OuterCellModel.Correct (m : OuterCellModel) (p : OuterFourierPolynomial) : Prop :=
  ∀ t : ℝ, |(t-(m.center : ℝ))/(m.radius : ℝ)| ≤ 1 →
    |p.value t-(m.polynomial p).value t| ≤ (m.error : ℝ)

theorem OuterCellModel.correct_of_basis (m : OuterCellModel) (p : OuterFourierPolynomial)
    {basis : List LocalTrigApprox}
    (hb : ∀ a ∈ basis, a.Correct m.center m.radius)
    (hr : m.radius ≠ 0) (hcs : m.coefficients = p.compiledCoefficients basis)
    (he : p.compiledError basis ≤ m.error) : m.Correct p := by
  intro t ht
  have h := p.compiled_value_error hb hr ht
  have he' : (p.compiledError basis : ℝ) ≤ m.error := by exact_mod_cast he
  simpa only [polynomial, hcs] using h.trans he'

structure OuterIntegralLeaf where
  cell : ℕ
  left : ℚ
  right : ℚ
  bound : ℚ
  deriving Repr

def OuterIntegralLeaf.check (l : OuterIntegralLeaf) (p : OuterFourierPolynomial)
    (models : ℕ → OuterCellModel) (count : ℕ) : Bool :=
  let m := models l.cell
  decide (l.cell < count ∧ 0 < m.radius ∧ l.left ≤ l.right ∧
    m.center-m.radius ≤ l.left ∧ l.right ≤ m.center+m.radius) &&
  (m.polynomial p).positiveIntegralUpperCheck l.left l.right m.error l.bound

theorem OuterIntegralLeaf.check_sound {l : OuterIntegralLeaf} {p : OuterFourierPolynomial}
    {models : ℕ → OuterCellModel} {count : ℕ}
    (hm : ∀ j < count, (models j).Correct p)
    (hc : l.check p models count = true) :
    (∫ t in (l.left : ℝ)..(l.right : ℝ), max (p.value t) 0) ≤ (l.bound : ℝ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc.1 with ⟨hj,hr,hlr,hl,hu⟩
  let m := models l.cell
  have hr' : (0 : ℝ) < m.radius := by exact_mod_cast hr
  have hrad : (m.polynomial p).radius ≠ 0 := ne_of_gt hr
  apply (m.polynomial p).positiveIntegralUpperCheck_sound l.left l.right m.error l.bound
    hrad hlr p.continuous _ hc.2
  intro t ht
  apply hm l.cell hj
  have hl' : (m.center : ℝ)-(m.radius : ℝ) ≤ l.left := by exact_mod_cast hl
  have hu' : (l.right : ℝ) ≤ (m.center : ℝ)+(m.radius : ℝ) := by exact_mod_cast hu
  rw [abs_div, abs_of_pos hr', div_le_iff₀ hr']
  apply abs_le.mpr
  constructor <;> linarith [ht.1,ht.2]

def outerLeafTotal : List OuterIntegralLeaf → ℚ
  | [] => 0
  | l :: ls => l.bound+outerLeafTotal ls

def outerChainCheck (p : OuterFourierPolynomial) (models : ℕ → OuterCellModel) (count : ℕ) :
    ℚ → ℚ → List OuterIntegralLeaf → Bool
  | a, b, [] => decide (a=b)
  | a, b, l :: ls => decide (l.left=a) && l.check p models count &&
      outerChainCheck p models count l.right b ls

theorem outerChainCheck_sound {p : OuterFourierPolynomial} {models : ℕ → OuterCellModel}
    {count : ℕ} (hm : ∀ j < count, (models j).Correct p)
    {a b : ℚ} {leaves : List OuterIntegralLeaf}
    (hc : outerChainCheck p models count a b leaves = true) :
    (∫ t in (a : ℝ)..(b : ℝ), max (p.value t) 0) ≤ (outerLeafTotal leaves : ℝ) := by
  induction leaves generalizing a with
  | nil =>
    simp only [outerChainCheck, decide_eq_true_eq] at hc
    subst a
    simp only [intervalIntegral.integral_same, outerLeafTotal, Rat.cast_zero, le_refl]
  | cons l ls ih =>
    simp only [outerChainCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hl := OuterIntegralLeaf.check_sound hm hc.1.2
    have hrest := ih hc.2
    have hf : Continuous (fun t => max (p.value t) 0) := p.continuous.max continuous_const
    rw [← hc.1.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (l.left : ℝ) (l.right : ℝ))
      (hf.intervalIntegrable (l.right : ℝ) (b : ℝ))]
    simpa only [outerLeafTotal, Rat.cast_add] using add_le_add hl hrest

end
end ErdosOverlap
