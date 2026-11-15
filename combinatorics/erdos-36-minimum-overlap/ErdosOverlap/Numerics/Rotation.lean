/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FixedBox
public import Mathlib.Analysis.Complex.Norm

/-!
# Stable fixed-point complex rotation

The executable recurrence uses exact Euclidean integer division by `2^128`.
The proof controls each coordinate's rounding error by `1/S`, the complex
rounding error by `2/S`, and its accumulation under a contractive rounded step.
No floating arithmetic or numerical oracle appears in the proof.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def rotationStep (c s : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((c * p.1 - s * p.2) / fixedScale, (s * p.1 + c * p.2) / fixedScale)

@[expose] def rotationIter (c s : ℤ) (initial : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => initial
  | j + 1 => rotationStep c s (rotationIter c s initial j)

@[expose] noncomputable def rotationValue (p : ℤ × ℤ) : ℂ :=
  ⟨(p.1 : ℝ) / fixedScale, (p.2 : ℝ) / fixedScale⟩

@[expose] noncomputable def rotationFactor (c s : ℤ) : ℂ := rotationValue (c, s)

@[expose] def rotationRadius (E0 E1 : ℤ) (j : ℕ) : ℤ := E0 + (j : ℤ) * (E1 + 2)

@[expose] def rotationCoordinateBox (u E : ℤ) : FixedBox := ⟨u - E, u + E⟩

/-- Euclidean division supplies the exact rounding enclosure, even for negative numerators. -/
theorem rotation_floor_error (n : ℤ) :
    |((n / fixedScale : ℤ) : ℝ) / fixedScale - (n : ℝ) / (fixedScale : ℝ) ^ 2| ≤
      1 / (fixedScale : ℝ) := by
  have hS : (fixedScale : ℝ) ≠ 0 := ne_of_gt fixedScale_real_pos
  have hdec : ((n / fixedScale : ℤ) : ℝ) * fixedScale + (n % fixedScale : ℤ) = n := by
    exact_mod_cast Int.ediv_mul_add_emod n fixedScale
  have hr0 : (0 : ℝ) ≤ (n % fixedScale : ℤ) := by
    exact_mod_cast Int.emod_nonneg n (ne_of_gt fixedScale_pos)
  have hr1 : ((n % fixedScale : ℤ) : ℝ) ≤ fixedScale := by
    exact_mod_cast (Int.emod_lt_of_pos n fixedScale_pos).le
  have heq : ((n / fixedScale : ℤ) : ℝ) / fixedScale - (n : ℝ) / (fixedScale : ℝ) ^ 2 =
      -((n % fixedScale : ℤ) : ℝ) / (fixedScale : ℝ) ^ 2 := by
    field_simp [hS]
    nlinarith [hdec]
  rw [heq, abs_div, abs_neg, abs_of_nonneg hr0, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (fixedScale : ℝ) / (fixedScale : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hr1 (sq_nonneg _)
    _ = _ := by field_simp [hS]

theorem rotationFactor_norm_le_one {c s : ℤ}
    (hcs : c ^ 2 + s ^ 2 ≤ fixedScale ^ 2) : ‖rotationFactor c s‖ ≤ 1 := by
  have hcsR : (c : ℝ) ^ 2 + (s : ℝ) ^ 2 ≤ (fixedScale : ℝ) ^ 2 := by
    exact_mod_cast hcs
  have hs : ‖rotationFactor c s‖ ^ 2 =
      ((c : ℝ) ^ 2 + (s : ℝ) ^ 2) / (fixedScale : ℝ) ^ 2 := by
    rw [Complex.sq_norm]
    simp only [rotationFactor, rotationValue, Complex.normSq_apply]
    ring
  have hle : ‖rotationFactor c s‖ ^ 2 ≤ 1 := by
    rw [hs]
    exact (div_le_one (sq_pos_of_pos fixedScale_real_pos)).mpr hcsR
  nlinarith [norm_nonneg (rotationFactor c s)]

theorem rotationStep_real_error (c s : ℤ) (p : ℤ × ℤ) :
    |(rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).re| ≤
      1 / (fixedScale : ℝ) := by
  have h := rotation_floor_error (c * p.1 - s * p.2)
  have heq : (rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).re =
      (((c * p.1 - s * p.2) / fixedScale : ℤ) : ℝ) / fixedScale -
        ((c * p.1 - s * p.2 : ℤ) : ℝ) / (fixedScale : ℝ) ^ 2 := by
    simp only [rotationStep, rotationFactor, rotationValue, Complex.sub_re, Complex.mul_re,
      Int.cast_sub, Int.cast_mul]
    ring
  rw [heq]
  exact h

theorem rotationStep_imag_error (c s : ℤ) (p : ℤ × ℤ) :
    |(rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).im| ≤
      1 / (fixedScale : ℝ) := by
  have h := rotation_floor_error (s * p.1 + c * p.2)
  have heq : (rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).im =
      (((s * p.1 + c * p.2) / fixedScale : ℤ) : ℝ) / fixedScale -
        ((s * p.1 + c * p.2 : ℤ) : ℝ) / (fixedScale : ℝ) ^ 2 := by
    simp only [rotationStep, rotationFactor, rotationValue, Complex.sub_im, Complex.mul_im,
      Int.cast_add, Int.cast_mul]
    ring
  rw [heq]
  exact h

theorem rotationStep_error (c s : ℤ) (p : ℤ × ℤ) :
    ‖rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p‖ ≤
      2 / (fixedScale : ℝ) := by
  calc
    _ ≤ |(rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).re| +
        |(rotationValue (rotationStep c s p) - rotationFactor c s * rotationValue p).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (fixedScale : ℝ) + 1 / (fixedScale : ℝ) :=
      add_le_add (rotationStep_real_error c s p) (rotationStep_imag_error c s p)
    _ = _ := by ring

theorem complex_norm_sub_le_of_coordinate_bounds {u z : ℂ} {er ei : ℝ}
    (hr : |u.re - z.re| ≤ er) (hi : |u.im - z.im| ≤ ei) : ‖u - z‖ ≤ er + ei := by
  exact (Complex.norm_le_abs_re_add_abs_im (u - z)).trans (add_le_add hr hi)

/-- A contractive approximate multiplier gives additive, not multiplicative, error growth. -/
theorem complex_rotation_step_bound {W Z x y next : ℂ} {e δ : ℝ}
    (hW : ‖W‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hstep : ‖W - Z‖ ≤ e) (hround : ‖next - W * x‖ ≤ δ) :
    ‖next - Z * y‖ ≤ ‖x - y‖ + e + δ := by
  have heq : next - Z * y = (next - W * x) + W * (x - y) + (W - Z) * y := by ring
  have h₁ : ‖W * (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (x - y)]
  have h₂ : ‖(W - Z) * y‖ ≤ e := by
    rw [norm_mul]
    calc
      _ ≤ ‖W - Z‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ ≤ e := by simpa only [mul_one] using hstep
  rw [heq]
  have htri : ‖(next - W * x) + W * (x - y) + (W - Z) * y‖ ≤
      ‖next - W * x‖ + ‖W * (x - y)‖ + ‖(W - Z) * y‖ := norm_add₃_le
  linarith

/-- Generic stable rotation theorem, with an arbitrary true unit starting point. -/
theorem complex_rotation_sequence_error {W Z z0 : ℂ} {ε0 εstep δ : ℝ}
    (states : ℕ → ℂ) (hW : ‖W‖ ≤ 1) (hZ : ‖Z‖ = 1) (hz0 : ‖z0‖ = 1)
    (hinitial : ‖states 0 - z0‖ ≤ ε0) (hstep : ‖W - Z‖ ≤ εstep)
    (hround : ∀ j, ‖states (j + 1) - W * states j‖ ≤ δ) (j : ℕ) :
    ‖states j - Z ^ j * z0‖ ≤ ε0 + (j : ℝ) * (εstep + δ) := by
  induction j with
  | zero => simpa using hinitial
  | succ j ih =>
    have hy : ‖Z ^ j * z0‖ ≤ 1 := by simp only [norm_mul, norm_pow, hZ, hz0, one_pow, one_mul, le_refl]
    have h := complex_rotation_step_bound hW hy hstep (hround j)
    have hp : Z * (Z ^ j * z0) = Z ^ (j + 1) * z0 := by rw [pow_succ']; ring
    rw [hp] at h
    push_cast
    linarith

/-- Exact integer iteration inherits the uniform additive error estimate. -/
theorem rotationIter_error {c s : ℤ} (initial : ℤ × ℤ)
    {Z z0 : ℂ} {ε0 εstep : ℝ}
    (hcs : c ^ 2 + s ^ 2 ≤ fixedScale ^ 2)
    (hZ : ‖Z‖ = 1) (hz0 : ‖z0‖ = 1)
    (hinitial : ‖rotationValue initial - z0‖ ≤ ε0)
    (hstep : ‖rotationFactor c s - Z‖ ≤ εstep) (j : ℕ) :
    ‖rotationValue (rotationIter c s initial j) - Z ^ j * z0‖ ≤
      ε0 + (j : ℝ) * (εstep + 2 / (fixedScale : ℝ)) := by
  apply complex_rotation_sequence_error
    (fun j => rotationValue (rotationIter c s initial j))
    (rotationFactor_norm_le_one hcs) hZ hz0 hinitial hstep
  intro k
  exact rotationStep_error c s (rotationIter c s initial k)

theorem rotationIter_error_int {c s : ℤ} (initial : ℤ × ℤ)
    {Z z0 : ℂ} {E0 E1 : ℤ}
    (hcs : c ^ 2 + s ^ 2 ≤ fixedScale ^ 2)
    (hZ : ‖Z‖ = 1) (hz0 : ‖z0‖ = 1)
    (hinitial : ‖rotationValue initial - z0‖ ≤ (E0 : ℝ) / fixedScale)
    (hstep : ‖rotationFactor c s - Z‖ ≤ (E1 : ℝ) / fixedScale) (j : ℕ) :
    ‖rotationValue (rotationIter c s initial j) - Z ^ j * z0‖ ≤
      (rotationRadius E0 E1 j : ℝ) / fixedScale := by
  have h := rotationIter_error initial hcs hZ hz0 hinitial hstep j
  convert! h using 1
  simp only [rotationRadius, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

theorem rotationCoordinateBox_contains_of_error {u E : ℤ} {x : ℝ}
    (h : |(u : ℝ) / fixedScale - x| ≤ (E : ℝ) / fixedScale) :
    x ∈ rotationCoordinateBox u E := by
  have hb := abs_le.mp h
  have hlow := mul_le_mul_of_nonneg_right hb.1 fixedScale_real_pos.le
  have hupp := mul_le_mul_of_nonneg_right hb.2 fixedScale_real_pos.le
  change ((u - E : ℤ) : ℝ) ≤ x * fixedScale ∧ x * fixedScale ≤ ((u + E : ℤ) : ℝ)
  push_cast
  have hne := ne_of_gt fixedScale_real_pos
  simp only [sub_mul, neg_mul, div_mul_cancel₀ _ hne] at hlow hupp
  constructor <;> linarith

/-- Certified real and imaginary boxes for every exact serialized state. -/
theorem rotationIter_mem_boxes {c s : ℤ} (initial : ℤ × ℤ)
    {Z z0 : ℂ} {E0 E1 : ℤ}
    (hcs : c ^ 2 + s ^ 2 ≤ fixedScale ^ 2)
    (hZ : ‖Z‖ = 1) (hz0 : ‖z0‖ = 1)
    (hinitial : ‖rotationValue initial - z0‖ ≤ (E0 : ℝ) / fixedScale)
    (hstep : ‖rotationFactor c s - Z‖ ≤ (E1 : ℝ) / fixedScale) (j : ℕ) :
    (Z ^ j * z0).re ∈ rotationCoordinateBox (rotationIter c s initial j).1 (rotationRadius E0 E1 j) ∧
    (Z ^ j * z0).im ∈ rotationCoordinateBox (rotationIter c s initial j).2 (rotationRadius E0 E1 j) := by
  have he := rotationIter_error_int initial hcs hZ hz0 hinitial hstep j
  constructor
  · apply rotationCoordinateBox_contains_of_error
    exact (Complex.abs_re_le_norm _).trans he
  · apply rotationCoordinateBox_contains_of_error
    exact (Complex.abs_im_le_norm _).trans he

end
end ErdosOverlap.Numerics
