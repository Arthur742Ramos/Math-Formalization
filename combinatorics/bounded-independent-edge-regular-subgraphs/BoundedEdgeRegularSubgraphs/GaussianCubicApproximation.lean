module

public import BoundedEdgeRegularSubgraphs.GaussianCharacteristicStein
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-!
# Gaussian approximation from the cubic gradient product
-/

public section

open MeasureTheory ProbabilityTheory MvPolynomial

namespace BoundedEdgeRegularSubgraphs

/-- The Stein equation bounds the error at one by the mean absolute
discrepancy of the gradient product. -/
theorem norm_integral_realCharacter_sub_gaussian_le_of_stein {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (F Γ : X → ℝ)
    (hf : Integrable F P) (hg : Integrable Γ P) {m : ℝ} (hm : 0 ≤ m)
    (hstein : ∀ s : ℝ, (∫ x, (F x : ℂ) * realCharacter s (F x) ∂P) =
      ((s : ℂ) * Complex.I) * ∫ x, (Γ x : ℂ) * realCharacter s (F x) ∂P) :
    ‖(∫ x, realCharacter 1 (F x) ∂P) - (Real.exp (-m / 2) : ℂ)‖ ≤ ∫ x, |Γ x - m| ∂P := by
  let φ (s : ℝ) := ∫ x, realCharacter s (F x) ∂P
  let g (x : X) := Γ x - m
  let E (s : ℝ) := - (s : ℂ) * ∫ x, (g x : ℂ) * realCharacter s (F x) ∂P
  have hgi : Integrable g P := hg.sub (integrable_const m)
  have hchar (s : ℝ) : Integrable (fun x ↦ realCharacter s (F x)) P := by
    have hh := (continuous_realCharacter s).measurable.comp_aemeasurable hf.aemeasurable
    exact Integrable.of_bound hh.aestronglyMeasurable 1 (ae_of_all _ (fun _ ↦ (norm_realCharacter _ _).le))
  have hΓ (s : ℝ) : Integrable (fun x ↦ (Γ x : ℂ) * realCharacter s (F x)) P := by
    have hh := (Complex.continuous_ofReal.measurable.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
    apply hg.abs.mono' (hh.mul (hchar s).aestronglyMeasurable)
    exact ae_of_all _ (fun x ↦ by
      change ‖(Γ x : ℂ) * realCharacter s (F x)‖ ≤ |Γ x|
      rw [norm_mul, norm_realCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs])
  have hφ₀ : φ 0 = 1 := by simp [φ, realCharacter]
  have hder (s : ℝ) : HasDerivAt φ (-((m * s : ℝ) : ℂ) * φ s + E s) s := by
    have hd := hasDerivAt_integral_realCharacter P F hf s
    have hswap (x : X) : (F x : ℂ) * Complex.I * realCharacter s (F x) =
        Complex.I * ((F x : ℂ) * realCharacter s (F x)) := by ring
    simp_rw [hswap] at hd
    rw [integral_const_mul, hstein s] at hd
    have hsplit :
        (∫ x, (g x : ℂ) * realCharacter s (F x) ∂P) =
          (∫ x, (Γ x : ℂ) * realCharacter s (F x) ∂P) - (m : ℂ) * φ s := by
      have hpt (x : X) : (g x : ℂ) * realCharacter s (F x) =
          (Γ x : ℂ) * realCharacter s (F x) - (m : ℂ) * realCharacter s (F x) := by
        simp only [g, Complex.ofReal_sub, sub_mul]
      simp_rw [hpt]
      rw [integral_sub (hΓ s) ((hchar s).const_mul (m : ℂ)), integral_const_mul]
    convert hd using 1
    dsimp only [E]
    have hI : Complex.I * ((s : ℂ) * Complex.I) = -(s : ℂ) := by
      calc
        _ = (s : ℂ) * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq, mul_neg, mul_one]
    rw [hsplit, ← mul_assoc Complex.I, hI]
    push_cast
    ring
  have herr (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖E s‖ ≤ ∫ x, |g x| ∂P := by
    have h := norm_integral_le_integral_norm (μ := P) (fun x ↦ (g x : ℂ) * realCharacter s (F x))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_realCharacter, mul_one] at h
    dsimp only [E]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left h hs.1).trans
      (mul_le_of_le_one_left (integral_nonneg (fun _ ↦ abs_nonneg _)) hs.2)
  exact characteristic_gaussian_approximation φ E hm hφ₀ (fun s _ ↦ hder s) herr

/-- The cubic characteristic function agrees with the Gaussian
characteristic function up to the square root of the gradient-product variance. -/
theorem norm_integral_cubic_realCharacter_sub_gaussian_le {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) :
    let f := gaussianCubicPolynomial A a v
    let g := gaussianCubicAuxiliary A a v
    let γ := standardGaussianProduct (n + 1)
    let m := ∫ x, eval x f ^ 2 ∂γ
    ‖(∫ x, realCharacter 1 (eval x f) ∂γ) - (Real.exp (-m / 2) : ℂ)‖ ≤
      Real.sqrt (Var[fun x ↦ eval x (gaussianGradientProduct f g); γ]) := by
  let f := gaussianCubicPolynomial A a v
  let G := gaussianGradientProduct f (gaussianCubicAuxiliary A a v)
  let F (x : Fin (n + 1) → ℝ) := eval x f
  let Γ (x : Fin (n + 1) → ℝ) := eval x G
  let γ := standardGaussianProduct (n + 1)
  let m := ∫ x, F x ^ 2 ∂γ
  have hF : Integrable F γ := integrable_eval_standardGaussianProduct f
  have hG : Integrable Γ γ := integrable_eval_standardGaussianProduct G
  have hmean : (∫ x, Γ x ∂γ) = m := integral_gaussianCubic_gradientProduct_eq_secondMoment A a v
  have hmain := norm_integral_realCharacter_sub_gaussian_le_of_stein γ F Γ hF hG
    (m := m) (integral_nonneg (fun _ ↦ sq_nonneg _)) (integral_cubic_mul_realCharacter_eq A a v)
  refine hmain.trans ?_
  let W (x : Fin (n + 1) → ℝ) := |Γ x - m|
  have hW : Integrable W γ := (hG.sub (integrable_const m)).abs
  have hW' : Integrable (fun x ↦ W x ^ 2) γ := by
    have he (x : Fin (n + 1) → ℝ) : eval x ((G - C m) ^ 2) = W x ^ 2 := by
      simp only [map_pow, map_sub, eval_C, W, Γ, sq_abs]
    rw [← funext he]
    exact integrable_eval_standardGaussianProduct _
  have hJ := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    ((continuous_id.pow 2).continuousOn) isClosed_Ici
    (ae_of_all _ (fun x ↦ show W x ∈ Set.Ici 0 from abs_nonneg _)) hW hW'
  change (∫ x, W x ∂γ) ≤ Real.sqrt (Var[Γ; γ])
  rw [variance_eq_integral hG.aemeasurable, hmean]
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).2
  simpa only [W, Function.comp_apply, sq_abs] using hJ

end BoundedEdgeRegularSubgraphs
