/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativePolynomialPatch
public import ErdosOverlap.Numerics.LeafIntegrationAE

/-!
# Checked upper integrals of a positive part

The polynomial range supplies an affine majorant of its positive part.
Its integral is enclosed by exact fixed-point arithmetic. A true function
within `delta` of the polynomial adds only `delta * (hi-lo)` to the upper
return, including cells on which either function changes sign.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory Set

public section

@[expose] def PolynomialPiece.positiveIntegralUpperBox (p : PolynomialPiece)
    (lo hi delta : ℚ) : FixedBox :=
  let line := (p.rangeBox lo hi).positiveLine
  ((FixedBox.ofRat line.slope).mul (p.integralBox 1 0 lo hi)).add
    (FixedBox.ofRat (line.constant * (hi - lo) + delta * (hi - lo)))

@[expose] def PolynomialPiece.positiveIntegralUpperCheck (p : PolynomialPiece)
    (lo hi delta bound : ℚ) : Bool :=
  (p.positiveIntegralUpperBox lo hi delta).upperBoundedBy bound

theorem PolynomialPiece.positiveIntegral_majorant_mem_box (p : PolynomialPiece)
    (lo hi delta : ℚ) (hr : p.radius ≠ 0) :
    ((p.rangeBox lo hi).positiveLine.slope : ℝ) *
        (∫ t in (lo : ℝ)..(hi : ℝ), p.value t) +
      ((p.rangeBox lo hi).positiveLine.constant : ℝ) * ((hi : ℝ) - (lo : ℝ)) +
      (delta : ℝ) * ((hi : ℝ) - (lo : ℝ)) ∈
      p.positiveIntegralUpperBox lo hi delta := by
  have hp : (∫ t in (lo : ℝ)..(hi : ℝ), p.value t) ∈ p.integralBox 1 0 lo hi := by
    simpa only [Rat.cast_one, Rat.cast_zero, zero_mul, add_zero, one_mul] using
      p.integral_mem_box 1 0 lo hi hr
  have hm := FixedBox.mem_add
    (FixedBox.mem_mul (FixedBox.mem_ofRat (p.rangeBox lo hi).positiveLine.slope) hp)
    (FixedBox.mem_ofRat
      ((p.rangeBox lo hi).positiveLine.constant * (hi - lo) + delta * (hi - lo)))
  convert hm using 1 <;> simp only [PolynomialPiece.positiveIntegralUpperBox,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sub]
  all_goals ring

theorem PolynomialPiece.positiveIntegral_le_majorant_ae {f : ℝ → ℝ}
    (p : PolynomialPiece) (lo hi delta : ℚ) (hlr : lo ≤ hi)
    (hf : IntervalIntegrable (fun t => max (f t) 0) volume (lo : ℝ) (hi : ℝ))
    (he : ∀ᵐ t ∂volume.restrict (Ioo (lo : ℝ) (hi : ℝ)),
      |f t - p.value t| ≤ (delta : ℝ)) :
    (∫ t in (lo : ℝ)..(hi : ℝ), max (f t) 0) ≤
      ((p.rangeBox lo hi).positiveLine.slope : ℝ) *
        (∫ t in (lo : ℝ)..(hi : ℝ), p.value t) +
      ((p.rangeBox lo hi).positiveLine.constant : ℝ) * ((hi : ℝ) - (lo : ℝ)) +
      (delta : ℝ) * ((hi : ℝ) - (lo : ℝ)) := by
  let line := (p.rangeBox lo hi).positiveLine
  have hp := p.continuous.intervalIntegrable (μ := volume) (lo : ℝ) (hi : ℝ)
  have hg : IntervalIntegrable (fun t => line.value (p.value t))
      volume (lo : ℝ) (hi : ℝ) := by
    exact intervalIntegrable_const.add (hp.const_mul (line.slope : ℝ))
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (lo : ℝ) (hi : ℝ)),
      max (f t) 0 ≤ line.value (p.value t) + (delta : ℝ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo, he] with t ht het
    have hP : max (p.value t) 0 ≤ (line.slope : ℝ) * p.value t +
        (line.constant : ℝ) := by
      simpa only [line, RationalAffine.value, add_comm] using
        p.positiveLine_sound ⟨ht.1.le, ht.2.le⟩
    have h := positivePart_le_affine_of_approx het hP
    simpa only [RationalAffine.value, add_comm] using h
  have hm := integral_upper_of_ae_margin (by exact_mod_cast hlr) hf hg hpoint
  have hiLine : (∫ t in (lo : ℝ)..(hi : ℝ), line.value (p.value t)) =
      (line.constant : ℝ) * ((hi : ℝ) - (lo : ℝ)) +
        (line.slope : ℝ) * (∫ t in (lo : ℝ)..(hi : ℝ), p.value t) := by
    unfold RationalAffine.value
    rw [intervalIntegral.integral_add intervalIntegrable_const (hp.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    ring
  rw [hiLine] at hm
  convert hm using 1
  simp only [line]
  ring

theorem PolynomialPiece.positiveIntegral_upper_ae {f : ℝ → ℝ}
    (p : PolynomialPiece) (lo hi delta : ℚ) (hr : p.radius ≠ 0) (hlr : lo ≤ hi)
    (hf : IntervalIntegrable (fun t => max (f t) 0) volume (lo : ℝ) (hi : ℝ))
    (he : ∀ᵐ t ∂volume.restrict (Ioo (lo : ℝ) (hi : ℝ)),
      |f t - p.value t| ≤ (delta : ℝ)) :
    (∫ t in (lo : ℝ)..(hi : ℝ), max (f t) 0) ≤
      ((p.positiveIntegralUpperBox lo hi delta).upperRat : ℝ) := by
  exact (p.positiveIntegral_le_majorant_ae lo hi delta hlr hf he).trans
    (FixedBox.real_bounds (p.positiveIntegral_majorant_mem_box lo hi delta hr)).2

theorem PolynomialPiece.positiveIntegralUpperCheck_sound_ae {f : ℝ → ℝ}
    (p : PolynomialPiece) (lo hi delta bound : ℚ)
    (hr : p.radius ≠ 0) (hlr : lo ≤ hi)
    (hf : IntervalIntegrable (fun t => max (f t) 0) volume (lo : ℝ) (hi : ℝ))
    (he : ∀ᵐ t ∂volume.restrict (Ioo (lo : ℝ) (hi : ℝ)),
      |f t - p.value t| ≤ (delta : ℝ))
    (hc : p.positiveIntegralUpperCheck lo hi delta bound = true) :
    (∫ t in (lo : ℝ)..(hi : ℝ), max (f t) 0) ≤ (bound : ℝ) := by
  exact (p.positiveIntegral_le_majorant_ae lo hi delta hlr hf he).trans
    (FixedBox.upperBoundedBy_sound
      (p.positiveIntegral_majorant_mem_box lo hi delta hr) hc)

theorem PolynomialPiece.positiveIntegralUpperCheck_sound {f : ℝ → ℝ}
    (p : PolynomialPiece) (lo hi delta bound : ℚ)
    (hr : p.radius ≠ 0) (hlr : lo ≤ hi) (hf : Continuous f)
    (he : ∀ t ∈ Icc (lo : ℝ) (hi : ℝ), |f t - p.value t| ≤ (delta : ℝ))
    (hc : p.positiveIntegralUpperCheck lo hi delta bound = true) :
    (∫ t in (lo : ℝ)..(hi : ℝ), max (f t) 0) ≤ (bound : ℝ) := by
  apply p.positiveIntegralUpperCheck_sound_ae lo hi delta bound hr hlr
    ((hf.max continuous_const).intervalIntegrable (μ := volume) (lo : ℝ) (hi : ℝ)) _ hc
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  exact he t ⟨ht.1.le, ht.2.le⟩

end
end ErdosOverlap.Numerics
