module

public import BoundedEdgeRegularSubgraphs.GaussianCharacteristicODE
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Differentiating the Gaussian characteristic function
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- A real argument in the scalar complex character. -/
@[expose] noncomputable def realCharacter (s x : ℝ) : ℂ := Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)

theorem norm_realCharacter (s x : ℝ) : ‖realCharacter s x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_realCharacter (s : ℝ) : Continuous (realCharacter s) := by
  unfold realCharacter
  fun_prop

private theorem hasDerivAt_realCharacter (s x : ℝ) :
    HasDerivAt (fun t ↦ realCharacter t x) ((x : ℂ) * Complex.I * realCharacter s x) s := by
  have hu : HasDerivAt (fun t : ℝ ↦ t * x) x s := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id s).mul_const x
  have hc := ((Real.hasDerivAt_cos (s * x)).comp s hu).ofReal_comp
  have hs := ((Real.hasDerivAt_sin (s * x)).comp s hu).ofReal_comp
  have h := hc.fun_add (hs.mul_const Complex.I)
  have hfun : (fun t : ℝ ↦ realCharacter t x) =
      fun t ↦ (Real.cos (t * x) : ℂ) + (Real.sin (t * x) : ℂ) * Complex.I := by
    funext t
    exact Complex.exp_ofReal_mul_I (t * x)
  rw [hfun]
  have hval : (x : ℂ) * Complex.I * realCharacter s x =
      ((-Real.sin (s * x) * x : ℝ) : ℂ) + ((Real.cos (s * x) * x : ℝ) : ℂ) * Complex.I := by
    rw [realCharacter, Complex.exp_ofReal_mul_I, mul_add,
      show (x : ℂ) * Complex.I * ((Real.sin (s * x) : ℂ) * Complex.I) =
        (x : ℂ) * (Real.sin (s * x) : ℂ) * Complex.I ^ 2 by ring, Complex.I_sq]
    push_cast
    ring
  rw [hval]
  simpa only [Function.comp_apply] using h

/-- The characteristic function of an integrable real random variable
is differentiable on the real line. -/
theorem hasDerivAt_integral_realCharacter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Integrable F μ) (s : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, realCharacter t (F x) ∂μ)
      (∫ x, (F x : ℂ) * Complex.I * realCharacter s (F x) ∂μ) s := by
  have hm (t : ℝ) : AEStronglyMeasurable (fun x ↦ realCharacter t (F x)) μ :=
    ((continuous_realCharacter t).measurable.comp_aemeasurable hF.aemeasurable).aestronglyMeasurable
  have hFi : Integrable (fun x ↦ realCharacter s (F x)) μ :=
    Integrable.of_bound (hm s) 1 (ae_of_all _ (fun _ ↦ (norm_realCharacter _ _).le))
  have hd : AEStronglyMeasurable (fun x ↦ (F x : ℂ) * Complex.I * realCharacter s (F x)) μ :=
    (((Complex.continuous_ofReal.measurable.comp_aemeasurable hF.aemeasurable).aestronglyMeasurable).mul
      aestronglyMeasurable_const).mul (hm s)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (univ_mem : Set.univ ∈ 𝓝 s)
    (Eventually.of_forall hm) hFi hd
    (ae_of_all _ (fun x t _ ↦ by
      rw [norm_mul, norm_mul, Complex.norm_I, norm_realCharacter, mul_one, mul_one, Complex.norm_real]))
    hF.norm
    (ae_of_all _ (fun x t _ ↦ hasDerivAt_realCharacter t (F x)))
  exact h.2

end BoundedEdgeRegularSubgraphs
