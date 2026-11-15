/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.RotationGrid
public import ErdosOverlap.Numerics.TaylorModel

/-!
# Exact integer certificates for quantized Taylor coefficients

The rational frequency factors are checked once per degree. Each subsequent
coefficient check uses only an integer dot product, the stored factor mass,
and the proved rotation error. No floating-point computation is trusted.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def taylorGridCenter (j : ℕ) : ℚ := ((2 * j + 1 : ℕ) : ℚ) / 1024

@[expose] def taylorGridRadius : ℚ := 1 / 1024

@[expose] def taylorFactorRat (term : CosineTerm) (k : ℕ) : ℚ :=
  (if k % 4 = 0 ∨ k % 4 = 3 then 1 else -1) *
    term.weight * (term.frequency / 1024) ^ k / (k.factorial : ℚ)

@[expose] def factorRowCheck : List CosineTerm → ℕ → List ℤ → Bool
  | [], _, [] => true
  | term :: terms, k, f :: fs =>
      decide (f = (taylorFactorRat term k * (fixedScale : ℚ)).floor) &&
        factorRowCheck terms k fs
  | _, _, _ => false

@[expose] noncomputable def FactorRowCorrect (terms : List CosineTerm)
    (k : ℕ) (factors : List ℤ) : Prop :=
  List.Forall₂ (fun (term : CosineTerm) (f : ℤ) =>
    |(fixedScale : ℝ) * (taylorFactorRat term k : ℝ) - (f : ℝ)| ≤ 1) terms factors

@[expose] def taylorCoordinate (state : ℤ × ℤ) (k : ℕ) : ℤ :=
  if k % 2 = 0 then state.1 else state.2

@[expose] noncomputable def taylorTrig (frequency : ℚ) (j k : ℕ) : ℝ :=
  if k % 2 = 0 then
    Real.cos ((frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ)
  else Real.sin ((frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ)

@[expose] def taylorDot : List ℤ → List (ℤ × ℤ) → ℕ → ℤ
  | [], [], _ => 0
  | f :: fs, state :: row, k => f * taylorCoordinate state k + taylorDot fs row k
  | _, _, _ => 0

@[expose] def taylorFactorMass : List ℤ → ℤ
  | [] => 0
  | f :: fs => |f| + taylorFactorMass fs

@[expose] def quantizedCoefficientScale : ℤ := 1152921504606846976

@[expose] def quantizedCoefficientToleranceDenominator : ℤ := 100000000000000

@[expose] def coefficientCheck (factors : List ℤ) (row : List (ℤ × ℤ))
    (j k : ℕ) (p : ℤ) : Bool :=
  decide (factors.length = row.length ∧
    |taylorDot factors row k - p * (fixedScale ^ 2 / quantizedCoefficientScale)| +
      taylorFactorMass factors * rotationRadius rotationSeedError rotationSeedError j +
      (factors.length : ℤ) * fixedScale ≤
        fixedScale ^ 2 / quantizedCoefficientToleranceDenominator)

@[expose] noncomputable def cosineLocalCoefficientSum :
    List CosineTerm → ℚ → ℚ → ℕ → ℝ
  | [], _, _, _ => 0
  | term :: terms, center, radius, k =>
      term.localCoefficient center radius k +
        cosineLocalCoefficientSum terms center radius k

theorem scaled_floor_error (q : ℚ) :
    |(fixedScale : ℝ) * (q : ℝ) -
      ((q * (fixedScale : ℚ)).floor : ℝ)| ≤ 1 := by
  have hl := Int.floor_le (q * (fixedScale : ℚ))
  have hu := (Int.lt_floor_add_one (q * (fixedScale : ℚ))).le
  have hl' : (((q * (fixedScale : ℚ)).floor : ℤ) : ℝ) ≤
      (q : ℝ) * (fixedScale : ℝ) := by exact_mod_cast hl
  have hu' : (q : ℝ) * (fixedScale : ℝ) ≤
      (((q * (fixedScale : ℚ)).floor : ℤ) : ℝ) + 1 := by exact_mod_cast hu
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem factorRowCheck_sound {terms : List CosineTerm} {k : ℕ} {factors : List ℤ}
    (h : factorRowCheck terms k factors = true) : FactorRowCorrect terms k factors := by
  induction terms generalizing factors with
  | nil =>
    cases factors with
    | nil => exact List.Forall₂.nil
    | cons f fs => simp [factorRowCheck] at h
  | cons term terms ih =>
    cases factors with
    | nil => simp [factorRowCheck] at h
    | cons f fs =>
      simp only [factorRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      apply List.Forall₂.cons
      · rw [h.1]
        exact scaled_floor_error _
      · exact ih h.2

theorem localCoefficient_grid_eq (term : CosineTerm) (j k : ℕ) :
    term.localCoefficient (taylorGridCenter j) taylorGridRadius k =
      (taylorFactorRat term k : ℝ) * taylorTrig term.frequency j k := by
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h1 | h2 | h3
  all_goals
    have hpar : k % 2 = (k % 4) % 2 := by omega
    simp only [CosineTerm.localCoefficient, taylorGridCenter, taylorGridRadius,
      taylorFactorRat, taylorTrig, cosineCycle, hpar]
  · simp only [h0]
    norm_num
    ring_nf
  · simp only [h1]
    norm_num
    ring_nf
  · simp only [h2]
    norm_num
    ring_nf
  · simp only [h3]
    norm_num
    ring_nf

theorem abs_taylorTrig_le_one (frequency : ℚ) (j k : ℕ) :
    |taylorTrig frequency j k| ≤ 1 := by
  unfold taylorTrig
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

theorem taylorCoordinate_scaled_error {term : CosineTerm} {state : ℤ × ℤ} {j : ℕ}
    (h : Real.cos ((term.frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
        rotationCoordinateBox state.1 (rotationRadius rotationSeedError rotationSeedError j) ∧
      Real.sin ((term.frequency * ((2 * j + 1 : ℕ) : ℚ) / 1024 : ℚ) : ℝ) ∈
        rotationCoordinateBox state.2 (rotationRadius rotationSeedError rotationSeedError j))
    (k : ℕ) :
    |(fixedScale : ℝ) * taylorTrig term.frequency j k -
      (taylorCoordinate state k : ℝ)| ≤
      (rotationRadius rotationSeedError rotationSeedError j : ℝ) := by
  have hc := h.1
  have hs := h.2
  change ((state.1 - rotationRadius rotationSeedError rotationSeedError j : ℤ) : ℝ) ≤
      _ * (fixedScale : ℝ) ∧ _ * (fixedScale : ℝ) ≤
      ((state.1 + rotationRadius rotationSeedError rotationSeedError j : ℤ) : ℝ) at hc
  change ((state.2 - rotationRadius rotationSeedError rotationSeedError j : ℤ) : ℝ) ≤
      _ * (fixedScale : ℝ) ∧ _ * (fixedScale : ℝ) ≤
      ((state.2 + rotationRadius rotationSeedError rotationSeedError j : ℤ) : ℝ) at hs
  simp only [Int.cast_sub, Int.cast_add] at hc hs
  unfold taylorTrig taylorCoordinate
  split_ifs
  · exact abs_le.mpr ⟨by nlinarith [hc.1], by nlinarith [hc.2]⟩
  · exact abs_le.mpr ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩

theorem quantized_product_scaled_error {a t : ℝ} {f u E : ℤ}
    (ha : |(fixedScale : ℝ) * a - f| ≤ 1)
    (ht : |(fixedScale : ℝ) * t - u| ≤ E)
    (htone : |t| ≤ 1) :
    |(fixedScale : ℝ) ^ 2 * (a * t) - (f : ℝ) * u| ≤
      |(f : ℝ)| * (E : ℝ) + fixedScale := by
  have hSt : |(fixedScale : ℝ) * t| ≤ fixedScale := by
    rw [abs_mul, abs_of_pos fixedScale_real_pos]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left htone fixedScale_real_pos.le
  have hfirst : |((fixedScale : ℝ) * a - f) * ((fixedScale : ℝ) * t)| ≤
      fixedScale := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans
      (by simpa only [one_mul] using hSt)
  have hsecond : |(f : ℝ) * ((fixedScale : ℝ) * t - u)| ≤ |(f : ℝ)| * (E : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have he : (fixedScale : ℝ) ^ 2 * (a * t) - (f : ℝ) * u =
      ((fixedScale : ℝ) * a - f) * ((fixedScale : ℝ) * t) +
        (f : ℝ) * ((fixedScale : ℝ) * t - u) := by ring
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans_eq (add_comm _ _)

/-- The full row error is proved with scaled real arithmetic; the displayed
right-hand side is an exact integer expression. -/
theorem quantizedTaylor_scaled_error {terms : List CosineTerm} {factors : List ℤ}
    {row : List (ℤ × ℤ)} {j k : ℕ}
    (hf : FactorRowCorrect terms k factors) (hr : RowTrigCorrect terms row j) :
    |(fixedScale : ℝ) ^ 2 *
        cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k -
      (taylorDot factors row k : ℝ)| ≤
      ((taylorFactorMass factors * rotationRadius rotationSeedError rotationSeedError j +
        (factors.length : ℤ) * fixedScale : ℤ) : ℝ) := by
  unfold FactorRowCorrect at hf
  unfold RowTrigCorrect at hr
  induction hf generalizing row with
  | nil =>
    cases hr
    simp only [cosineLocalCoefficientSum, taylorDot, taylorFactorMass, List.length_nil,
      Nat.cast_zero, zero_mul, mul_zero, add_zero, Int.cast_zero, sub_self, abs_zero, le_refl]
  | @cons term f terms factors hfactor htail ih =>
    cases hr with
    | @cons _ state _ row htrig hrest =>
      have hi := ih hrest
      have ht := taylorCoordinate_scaled_error htrig k
      have hp := quantized_product_scaled_error hfactor ht
        (abs_taylorTrig_le_one term.frequency j k)
      rw [← localCoefficient_grid_eq] at hp
      have he : (fixedScale : ℝ) ^ 2 *
          cosineLocalCoefficientSum (term :: terms) (taylorGridCenter j) taylorGridRadius k -
          (taylorDot (f :: factors) (state :: row) k : ℝ) =
          ((fixedScale : ℝ) ^ 2 * term.localCoefficient (taylorGridCenter j) taylorGridRadius k -
            (f : ℝ) * taylorCoordinate state k) +
          ((fixedScale : ℝ) ^ 2 *
            cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k -
            (taylorDot factors row k : ℝ)) := by
        simp only [cosineLocalCoefficientSum, taylorDot, Int.cast_add, Int.cast_mul]
        ring
      rw [he]
      apply ((abs_add_le _ _).trans (add_le_add hp hi)).trans_eq
      simp only [taylorFactorMass, List.length_cons, Int.cast_add, Int.cast_mul,
        Int.cast_abs, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      ring

theorem quantizedCoefficientScale_pos : 0 < quantizedCoefficientScale := by
  norm_num [quantizedCoefficientScale]

theorem quantizedCoefficientScale_real_pos : (0 : ℝ) < quantizedCoefficientScale := by
  exact_mod_cast quantizedCoefficientScale_pos

theorem quantizedCoefficientScale_divides :
    (fixedScale ^ 2 / quantizedCoefficientScale) * quantizedCoefficientScale =
      fixedScale ^ 2 := by
  norm_num [fixedScale, quantizedCoefficientScale]

/-- The checked integer tolerance is below the true scaled tolerance. -/
theorem coefficientTolerance_floor_le :
    ((fixedScale ^ 2 / quantizedCoefficientToleranceDenominator : ℤ) : ℝ) ≤
      (fixedScale : ℝ) ^ 2 / (quantizedCoefficientToleranceDenominator : ℝ) := by
  have hden : 0 < quantizedCoefficientToleranceDenominator := by
    norm_num [quantizedCoefficientToleranceDenominator]
  have h := Int.ediv_mul_le (fixedScale ^ 2) (ne_of_gt hden)
  have hc : ((fixedScale ^ 2 / quantizedCoefficientToleranceDenominator : ℤ) : ℝ) *
      (quantizedCoefficientToleranceDenominator : ℝ) ≤ (fixedScale : ℝ) ^ 2 := by
    exact_mod_cast h
  exact (le_div_iff₀ (by exact_mod_cast hden)).mpr hc

/-- Final dot-product interface: a successful integer comparison proves the
actual real Taylor coefficient is within `10⁻¹⁴` of `p/2⁶⁰`. -/
theorem coefficientCheck_sound {terms : List CosineTerm} {factors : List ℤ}
    {row : List (ℤ × ℤ)} {j k : ℕ} {p : ℤ}
    (hf : FactorRowCorrect terms k factors) (hr : RowTrigCorrect terms row j)
    (hcheck : coefficientCheck factors row j k p = true) :
    |cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k -
      (p : ℝ) / (quantizedCoefficientScale : ℝ)| ≤
      1 / (quantizedCoefficientToleranceDenominator : ℝ) := by
  simp only [coefficientCheck, decide_eq_true_eq] at hcheck
  have herr := quantizedTaylor_scaled_error hf hr
  have hcheck' :
      |(taylorDot factors row k : ℝ) - (p : ℝ) *
        ((fixedScale ^ 2 / quantizedCoefficientScale : ℤ) : ℝ)| +
      ((taylorFactorMass factors * rotationRadius rotationSeedError rotationSeedError j +
        (factors.length : ℤ) * fixedScale : ℤ) : ℝ) ≤
      ((fixedScale ^ 2 / quantizedCoefficientToleranceDenominator : ℤ) : ℝ) := by
    have hc := hcheck.2
    rw [add_assoc] at hc
    exact_mod_cast hc
  have hdiv : ((fixedScale ^ 2 / quantizedCoefficientScale : ℤ) : ℝ) *
      (quantizedCoefficientScale : ℝ) = (fixedScale : ℝ) ^ 2 := by
    exact_mod_cast quantizedCoefficientScale_divides
  have hcenter : (p : ℝ) * ((fixedScale ^ 2 / quantizedCoefficientScale : ℤ) : ℝ) =
      (fixedScale : ℝ) ^ 2 * ((p : ℝ) / (quantizedCoefficientScale : ℝ)) := by
    apply (mul_right_cancel₀ (ne_of_gt quantizedCoefficientScale_real_pos))
    rw [mul_assoc, hdiv, mul_assoc, div_mul_cancel₀ _
      (ne_of_gt quantizedCoefficientScale_real_pos)]
    ring
  have hscaled : |(fixedScale : ℝ) ^ 2 *
      (cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k -
        (p : ℝ) / (quantizedCoefficientScale : ℝ))| ≤
      (fixedScale : ℝ) ^ 2 / (quantizedCoefficientToleranceDenominator : ℝ) := by
    have ht := abs_sub_le
      ((fixedScale : ℝ) ^ 2 *
        cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k)
      (taylorDot factors row k : ℝ)
      ((p : ℝ) * ((fixedScale ^ 2 / quantizedCoefficientScale : ℤ) : ℝ))
    rw [hcenter] at ht hcheck'
    rw [mul_sub]
    apply le_trans ?_ coefficientTolerance_floor_le
    have hadd := add_le_add herr (le_refl
      |(taylorDot factors row k : ℝ) -
        (fixedScale : ℝ) ^ 2 * ((p : ℝ) / (quantizedCoefficientScale : ℝ))|)
    exact ht.trans (hadd.trans (by linarith [hcheck']))
  rw [abs_mul, abs_of_nonneg (sq_nonneg (fixedScale : ℝ))] at hscaled
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos fixedScale_real_pos)).mp
  convert hscaled using 1
  ring

end
end ErdosOverlap.Numerics
