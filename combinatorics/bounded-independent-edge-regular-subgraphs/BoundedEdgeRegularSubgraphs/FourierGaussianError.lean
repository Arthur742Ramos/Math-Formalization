module

public import BoundedEdgeRegularSubgraphs.FourierSmallBoxGaussianIdentity
public import BoundedEdgeRegularSubgraphs.FourierGaussianAssembly
import Mathlib.Tactic

/-!
# Error estimate for the centred Fourier peak
-/

@[expose] public section

open MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The quartic correction evaluated in Gaussian coordinates. -/
noncomputable def phaseGaussianQuartic {n : ℕ} (A : Finset (Edge (Fin n)))
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) (x : Fin n → ℝ) : ℝ :=
  edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) (((CFC.sqrt (degreeCovariance A q))⁻¹) *ᵥ x)

/-- The cubic correction evaluated in Gaussian coordinates. -/
noncomputable def phaseGaussianCubic {n : ℕ} (A : Finset (Edge (Fin n)))
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) (x : Fin n → ℝ) : ℝ :=
  edgeCubic A (fun e ↦ degreeCubicCoefficient (q e)) (((CFC.sqrt (degreeCovariance A q))⁻¹) *ᵥ x)

noncomputable def phaseGaussianQuarticMean {n : ℕ} (A : Finset (Edge (Fin n)))
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) : ℝ :=
  ∫ x, phaseGaussianQuartic A q x ∂standardGaussianProduct n

noncomputable def phaseGaussianCubicSecondMoment {n : ℕ} (A : Finset (Edge (Fin n)))
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) : ℝ :=
  ∫ x, phaseGaussianCubic A q x ^ 2 ∂standardGaussianProduct n

noncomputable def phaseGaussianBox {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    Set (Fin n → ℝ) :=
  {x | ((CFC.sqrt Q)⁻¹) *ᵥ x ∈ realPhaseBox (α := Fin n) r}

theorem measurableSet_phaseGaussianBox {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    MeasurableSet (phaseGaussianBox Q r) := by
  let B := (CFC.sqrt Q)⁻¹
  rw [show phaseGaussianBox Q r = ⋂ i, {x : Fin n → ℝ | |(B *ᵥ x) i| ≤ r} by
    ext x; simp [phaseGaussianBox, B, realPhaseBox]]
  apply MeasurableSet.iInter
  intro i
  apply measurableSet_le _ measurable_const
  change Measurable (fun x : Fin n → ℝ ↦ |∑ j, B i j * x j|)
  have hm : Measurable (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j) :=
    Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul (measurable_pi_apply j))
  exact continuous_abs.measurable.comp hm

/-- The error of the centred peak is bounded by the uniform Taylor error,
the L¹ error of the quartic weight, and the cubic characteristic error. -/
theorem norm_centered_peak_sub_le {n : ℕ} (q : Edge (Fin n) → Icc (0 : ℝ) 1)
    (d : Fin n → ℤ) (hd : ∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i)
    (hQ : (degreeCovariance Finset.univ q).PosDef) {r η ε₄ ε₃ M : ℝ}
    (hr : 0 ≤ r) (hr' : 2 * r ≤ 1 / 4) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hη : ∀ x ∈ realPhaseBox (α := Fin n) r, ‖degreeFourierLocalError Finset.univ q x‖ ≤ η)
    (hν : |phaseGaussianQuarticMean Finset.univ q| ≤ M)
    (h₄ : let U := phaseGaussianBox (degreeCovariance Finset.univ q) r
          let ν := phaseGaussianQuarticMean Finset.univ q
          (∫ x, |U.indicator (fun x ↦ Real.exp (phaseGaussianQuartic Finset.univ q x)) x -
            Real.exp ν| ∂standardGaussianProduct n) ≤ ε₄)
    (h₃ : let F := phaseGaussianCubic Finset.univ q
          let μ := phaseGaussianCubicSecondMoment Finset.univ q
          ‖(∫ x, realCharacter 1 (F x) ∂standardGaussianProduct n) -
            (Real.exp (-μ / 2) : ℂ)‖ ≤ ε₃) :
    let Q := degreeCovariance Finset.univ q
    let μ := phaseGaussianCubicSecondMoment Finset.univ q
    let ν := phaseGaussianQuarticMean Finset.univ q
    ‖(∫ t in phaseBox (0 : PhaseCircle) r, degreeFourier Finset.univ q d t ∂phaseLaw) -
        ((phaseGaussianScale Q * Real.exp (-μ / 2 + ν) : ℝ) : ℂ)‖ ≤
      phaseGaussianScale Q * (2 * η * (Real.exp M + ε₄) + ε₄ + Real.exp M * ε₃) := by
  let A : Finset (Edge (Fin n)) := Finset.univ
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let F := phaseGaussianCubic A q
  let H := phaseGaussianQuartic A q
  let γ := standardGaussianProduct n
  let U := phaseGaussianBox Q r
  let R (x : Fin n → ℝ) := U.indicator (fun z ↦ degreeFourierLocalError A q (B *ᵥ z)) x
  let u (x : Fin n → ℝ) := realCharacter 1 (F x)
  let w (x : Fin n → ℝ) := U.indicator (fun z ↦ Real.exp (H z)) x
  let ν := phaseGaussianQuarticMean A q
  let μ := phaseGaussianCubicSecondMoment A q
  let Ξ := phaseGaussianScale Q
  have hΞ : 0 ≤ Ξ := by dsimp only [Ξ]; rw [phaseGaussianScale_eq Q hQ]; positivity
  have hU : MeasurableSet U := measurableSet_phaseGaussianBox Q r
  have hB (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ (B *ᵥ x) i) := by
    change Continuous (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j)
    exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_apply j))
  have hF : Continuous F := by
    change Continuous (fun x : Fin n → ℝ ↦
      ∑ e ∈ A, degreeCubicCoefficient (q e) * ((B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2) ^ 3)
    exact continuous_finsetSum _ (fun e _ ↦ continuous_const.mul (((hB _).add (hB _)).pow 3))
  have hH : Continuous H := by
    change Continuous (fun x : Fin n → ℝ ↦
      ∑ e ∈ A, degreeQuarticCoefficient (q e) * ((B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2) ^ 4)
    exact continuous_finsetSum _ (fun e _ ↦ continuous_const.mul (((hB _).add (hB _)).pow 4))
  have hu : AEStronglyMeasurable u γ := ((continuous_realCharacter 1).comp hF).aestronglyMeasurable
  have hR : AEStronglyMeasurable R γ :=
    ((measurable_degreeFourierLocalError A q).comp
      (measurable_pi_iff.mpr (fun i ↦ (hB i).measurable)) |>.indicator hU).aestronglyMeasurable
  have hw₀ (x : Fin n → ℝ) : 0 ≤ w x := by
    by_cases hx : x ∈ U
    · unfold w
      rw [indicator_of_mem hx]
      exact Real.exp_nonneg _
    · simp only [w, indicator_of_notMem hx, le_refl]
  let C := (A.card : ℝ) * ((1 / 96) * (2 * r) ^ 4)
  have hC (x : Fin n → ℝ) : ‖w x‖ ≤ Real.exp C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw₀ x)]
    by_cases hx : x ∈ U
    · have hx' : B *ᵥ x ∈ realPhaseBox (α := Fin n) r := hx
      have he : (fun i ↦ clipRadius r ((B *ᵥ x) i)) = B *ᵥ x :=
        funext (fun i ↦ clipRadius_eq_of_abs_le (hx' i))
      unfold w
      rw [indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      refine (le_abs_self (H x)).trans ?_
      change |edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) (B *ᵥ x)| ≤ C
      rw [← he]
      exact abs_edgeQuartic_clip_le A _ (by norm_num) hr (fun e _ ↦ abs_degreeQuarticCoefficient_le (q e)) _
    · unfold w
      rw [indicator_of_notMem hx]
      exact Real.exp_nonneg _
  have hw : Integrable w γ := Integrable.of_bound
    (((Real.continuous_exp.comp hH).measurable.indicator hU).aestronglyMeasurable)
    _ (ae_of_all _ hC)
  have hwint : (∫ x, w x ∂γ) ≤ Real.exp M + ε₄ := by
    have h₄' : (∫ x, |w x - Real.exp ν| ∂γ) ≤ ε₄ := h₄
    have hi := (hw.sub (integrable_const (Real.exp ν))).abs
    have h := integral_mono (hw.sub (integrable_const _)) hi (fun x ↦ le_abs_self (w x - Real.exp ν))
    change (∫ x, w x - Real.exp ν ∂γ) ≤ ∫ x, |w x - Real.exp ν| ∂γ at h
    rw [integral_sub hw (integrable_const _), integral_const, probReal_univ, one_smul] at h
    linarith only [h.trans h₄', Real.exp_le_exp.mpr ((le_abs_self ν).trans hν)]
  have hRn (x : Fin n → ℝ) : ‖R x‖ ≤ η := by
    by_cases hx : x ∈ U
    · unfold R
      rw [indicator_of_mem hx]
      exact hη (B *ᵥ x) hx
    · simp only [R, indicator_of_notMem hx, norm_zero, hη₀]
  have hf := norm_integral_phase_weight_remainder_sub_le γ u R w hu hR hw (ae_of_all _ hw₀)
    (ae_of_all _ (fun x ↦ norm_realCharacter 1 (F x))) hη₁ (ae_of_all _ hRn)
    (Real.exp ν) (Real.exp (-μ / 2) : ℂ)
  have hform : (∫ t in phaseBox (0 : PhaseCircle) r, degreeFourier A q d t ∂phaseLaw) =
      (Ξ : ℂ) * ∫ x, u x * (w x : ℂ) * Complex.exp (R x) ∂γ := by
    rw [integral_degreeFourier_centered_smallBox_eq_gaussian q d hd hQ hr']
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x ↦ by
      change U.indicator (fun y ↦ u y * (Real.exp (H y) : ℂ) *
        Complex.exp (degreeFourierLocalError A q (B *ᵥ y))) x = _
      by_cases hx : x ∈ U
      · simp only [R, w, indicator_of_mem hx]
      · simp only [R, w, indicator_of_notMem hx, Complex.ofReal_zero, mul_zero, zero_mul])
  change ‖(∫ t in phaseBox (0 : PhaseCircle) r, degreeFourier A q d t ∂phaseLaw) -
    ((Ξ * Real.exp (-μ / 2 + ν) : ℝ) : ℂ)‖ ≤ _
  rw [hform, Real.exp_add, Complex.ofReal_mul, Complex.ofReal_mul, mul_comm
    (Real.exp (-μ / 2) : ℂ) (Real.exp ν : ℂ), ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΞ]
  apply mul_le_mul_of_nonneg_left _ hΞ
  rw [abs_of_nonneg (Real.exp_nonneg _)] at hf
  refine hf.trans (add_le_add (add_le_add ?_ h₄) ?_)
  · exact mul_le_mul_of_nonneg_left hwint (by positivity)
  · exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self ν).trans hν)) h₃ (norm_nonneg _)
      (Real.exp_nonneg _)

end BoundedEdgeRegularSubgraphs
