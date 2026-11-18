module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# The characteristic-function differential estimate
-/

public section

namespace BoundedEdgeRegularSubgraphs

/-- A characteristic function with the Gaussian differential equation up to
a uniformly bounded error has the corresponding Gaussian value at one. -/
theorem characteristic_gaussian_approximation (φ error : ℝ → ℂ) {μ σ : ℝ}
    (hμ : 0 ≤ μ) (hzero : φ 0 = 1)
    (hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (-((μ * t : ℝ) : ℂ) * φ t + error t) t)
    (herr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖error t‖ ≤ σ) :
    ‖φ 1 - (Real.exp (-μ / 2) : ℂ)‖ ≤ σ := by
  let E (t : ℝ) := Real.exp (μ * t ^ 2 / 2)
  let G (t : ℝ) := (E t : ℂ) * φ t
  have hE (t : ℝ) : HasDerivAt (fun s ↦ (E s : ℂ)) ((μ * t * E t : ℝ) : ℂ) t := by
    have hp : HasDerivAt (fun s ↦ μ * s ^ 2 / 2) (μ * t) t := by
      have hd := ((hasDerivAt_pow 2 t).const_mul μ).div_const (2 : ℝ)
      have hx : μ * (((2 : ℕ) : ℝ) * t ^ (2 - 1 : ℕ)) / 2 = μ * t := by norm_num; ring
      simpa only [hx] using hd
    have he := (Real.hasDerivAt_exp (μ * t ^ 2 / 2)).comp t hp
    change HasDerivAt (fun s ↦ (Real.exp (μ * s ^ 2 / 2) : ℂ)) _ t
    simpa only [E, Function.comp_apply, mul_comm] using he.ofReal_comp
  have hG (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt G ((E t : ℂ) * error t) t := by
    have hd := (hE t).fun_mul (hφ t ht)
    have hx : ((μ * t * E t : ℝ) : ℂ) * φ t +
        (E t : ℂ) * (-((μ * t : ℝ) : ℂ) * φ t + error t) =
          (E t : ℂ) * error t := by push_cast; ring
    rw [hx] at hd
    exact hd
  have hEpos (t : ℝ) : 0 < E t := Real.exp_pos _
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖(E t : ℂ) * error t‖ ≤ E 1 * σ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hEpos t).le]
    apply mul_le_mul _ (herr t ht) (norm_nonneg _) (hEpos 1).le
    unfold E
    apply Real.exp_le_exp.mpr
    have hsq : t ^ 2 ≤ 1 := by simpa using (sq_le_sq₀ ht.1 (by norm_num)).mpr ht.2
    nlinarith only [mul_le_mul_of_nonneg_left hsq hμ]
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht ↦ (hG t ht).hasDerivWithinAt) hderiv
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hG₀ : G 0 = 1 := by simp [G, E, hzero]
  have hE₁ : (E 1 : ℂ) * (Real.exp (-μ / 2) : ℂ) = 1 := by
    dsimp only [E]
    rw [one_pow, mul_one, ← Complex.ofReal_mul, ← Real.exp_add,
      show μ / 2 + -μ / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hfactor : G 1 - G 0 = (E 1 : ℂ) * (φ 1 - (Real.exp (-μ / 2) : ℂ)) := by
    rw [hG₀, mul_sub, hE₁]
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hEpos 1).le] at h
  simp only [sub_zero, norm_one, mul_one] at h
  exact le_of_mul_le_mul_left h (hEpos 1)

end BoundedEdgeRegularSubgraphs
