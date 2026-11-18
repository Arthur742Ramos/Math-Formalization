module

public import BoundedEdgeRegularSubgraphs.Fourier
import BoundedEdgeRegularSubgraphs.BernoulliFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Anti-concentration for a sum of independent Bernoulli variables

The scalar atom estimate used for the fresh edges in §3 and §8 follows
from circle inversion, Jordan's inequality and the Gaussian integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

universe u

variable {ι : Type u} [Fintype ι]

/-- Product law of a finite family of independent Bernoulli indicators. -/
noncomputable def bernoulliProduct (q : ι → Set.Icc (0 : ℝ) 1) : Measure (ι → ℝ) :=
  Measure.pi (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (q i))

instance (q : ι → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (bernoulliProduct q) := by
  unfold bernoulliProduct
  infer_instance

/-- Number of coordinates with value one. -/
noncomputable def bernoulliCount (w : ι → ℝ) : ℤ :=
  ∑ i, if w i = 1 then 1 else 0

/-- The count has the specified integer value. -/
noncomputable def countAtom (d : ℤ) : Set (ι → ℝ) :=
  {w | bernoulliCount w = d}

private theorem measurable_bernoulliCount : Measurable (bernoulliCount (ι := ι)) := by
  classical
  unfold bernoulliCount
  refine Finset.measurable_sum _ (fun i _ ↦ ?_)
  have hi : Measurable (fun w : ι → ℝ ↦ w i) := measurable_pi_apply i
  exact Measurable.ite ((measurableSet_singleton (1 : ℝ)).preimage hi)
    measurable_const measurable_const

omit [Fintype ι] in
private theorem fourier_sum_count (s : Finset ι) (r : ι → ℤ) (t : PhaseCircle) :
    fourier (∑ i ∈ s, r i) t = ∏ i ∈ s, fourier (r i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add, ih]

/-- The centred scalar characteristic function in product form. -/
noncomputable def countFourier (q : ι → Set.Icc (0 : ℝ) 1) (d : ℤ) (t : PhaseCircle) : ℂ :=
  fourier (-d) t * ∏ i, (1 - ((q i : ℝ) : ℂ) + ((q i : ℝ) : ℂ) * fourier 1 t)

private theorem integral_count_character (q : ι → Set.Icc (0 : ℝ) 1) (d : ℤ) (t : PhaseCircle) :
    ∫ w, fourier (bernoulliCount w - d) t ∂bernoulliProduct q = countFourier q d t := by
  classical
  simp_rw [bernoulliCount, sub_eq_add_neg, fourier_add, fourier_sum_count]
  have hmul (w : ι → ℝ) : (∏ i, fourier (if w i = 1 then 1 else 0) t) * fourier (-d) t =
      fourier (-d) t * ∏ i, fourier (if w i = 1 then 1 else 0) t := mul_comm _ _
  simp_rw [hmul]
  rw [integral_const_mul, bernoulliProduct,
    integral_fintype_prod_eq_prod (fun _ (x : ℝ) ↦ fourier (if x = 1 then (1 : ℤ) else 0) t)]
  unfold countFourier
  congr 1
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [integral_bernoulliMeasure]
  simp [Complex.real_smul]
  ring

/-- Exact scalar Fourier inversion under the normalized circle law. -/
theorem probability_countAtom_eq_integral (q : ι → Set.Icc (0 : ℝ) 1) (d : ℤ) :
    ((bernoulliProduct q).real (countAtom d) : ℂ) =
      ∫ t, countFourier q d t ∂AddCircle.haarAddCircle := by
  classical
  have hm : Measurable (fun (x : (ι → ℝ) × PhaseCircle) ↦
      fourier (bernoulliCount x.1 - d) x.2) := by
    have h : Measurable (fun x : ℤ × PhaseCircle ↦ fourier x.1 x.2) :=
      measurable_from_prod_countable_right (fun n ↦ (fourier n).continuous.measurable)
    exact h.comp (((measurable_bernoulliCount.comp measurable_fst).sub_const d).prodMk measurable_snd)
  have hi : Integrable (Function.uncurry fun w t ↦ fourier (bernoulliCount w - d) t)
      ((bernoulliProduct q).prod (AddCircle.haarAddCircle (T := 2 * Real.pi))) := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    exact ae_of_all _ (fun x ↦ by
      change ‖fourier (bernoulliCount x.1 - d) x.2‖ ≤ 1
      rw [fourier_apply, Circle.norm_coe])
  simp_rw [← integral_count_character q d]
  rw [← integral_integral_swap hi]
  simp_rw [integral_circle_fourier]
  have hind (w : ι → ℝ) :
      (if bernoulliCount w - d = 0 then (1 : ℂ) else 0) =
        (countAtom d).indicator (fun _ ↦ (1 : ℂ)) w := by
    by_cases h : bernoulliCount w = d <;> simp [countAtom, Set.indicator, sub_eq_zero, h]
  simp_rw [hind]
  have hmeas : MeasurableSet (countAtom (ι := ι) d) :=
    (measurableSet_singleton d).preimage measurable_bernoulliCount
  rw [integral_indicator_const 1 hmeas]
  simp [Complex.real_smul]

private theorem continuous_countFourier (q : ι → Set.Icc (0 : ℝ) 1) (d : ℤ) :
    Continuous (countFourier q d) := by
  unfold countFourier
  exact (fourier (-d)).continuous.mul
    (continuous_finsetProd _ (fun i _ ↦ continuous_const.add
      (continuous_const.mul (fourier 1).continuous)))

theorem fourier_one_coe (s : ℝ) :
    fourier 1 (s : PhaseCircle) = Complex.exp ((s : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem norm_countFourier_le (q : ι → Set.Icc (0 : ℝ) 1)
    (d : ℤ) (ξ : ℝ) (hq : ∀ i, ξ ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1 - ξ) (s : ℝ) :
    ‖countFourier q d (s : PhaseCircle)‖ ≤
      Real.exp (-2 * (Fintype.card ι : ℝ) * ξ * (1 - ξ) * Real.sin (s / 2) ^ 2) := by
  have hvar (i : ι) : ξ * (1 - ξ) ≤ (q i : ℝ) * (1 - q i) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hq i).1) (sub_nonneg.mpr (hq i).2)]
  calc
    ‖countFourier q d (s : PhaseCircle)‖ = ∏ i, ‖bernoulliFourierFactor (q i) s‖ := by
      have hn : ‖fourier (-d) (s : PhaseCircle)‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      rw [countFourier, norm_mul, hn, one_mul, Complex.norm_prod]
      exact Finset.prod_congr rfl (fun i _ ↦ by
        rw [fourier_one_coe]
        rfl)
    _ ≤ ∏ _ : ι, Real.exp (-2 * ξ * (1 - ξ) * Real.sin (s / 2) ^ 2) := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
        (bernoulliFourierFactor_norm_le _ _).trans (Real.exp_le_exp.mpr ?_))
      nlinarith only [mul_le_mul_of_nonneg_right (hvar i) (sq_nonneg (Real.sin (s / 2)))]
    _ = _ := by
      rw [← Real.exp_sum]
      simp [Finset.sum_const, nsmul_eq_mul]
      ring_nf

private theorem sin_half_sq_lower (s : ℝ) (hs : s ∈ Set.Ioc (-Real.pi) Real.pi) :
    s ^ 2 / Real.pi ^ 2 ≤ Real.sin (s / 2) ^ 2 := by
  have hhalf : |s / 2| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have h := Real.mul_abs_le_abs_sin hhalf
  have hz : 0 ≤ 2 / Real.pi * |s / 2| := by positivity
  have hsquare := (sq_le_sq₀ hz (abs_nonneg _)).mpr h
  rw [sq_abs, abs_div, show |(2 : ℝ)| = 2 by norm_num] at hsquare
  rw [show 2 / Real.pi * (|s| / 2) = |s| / Real.pi by ring, div_pow, sq_abs] at hsquare
  exact hsquare

/-- The quantitative scalar atom estimate, in its Gaussian-integral form. -/
theorem probability_countAtom_le_gaussian (q : ι → Set.Icc (0 : ℝ) 1)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2)
    (hq : ∀ i, ξ ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1 - ξ) (hm : 0 < Fintype.card ι) (d : ℤ) :
    (bernoulliProduct q).real (countAtom d) ≤
      (2 * Real.pi)⁻¹ * Real.sqrt
        (Real.pi / ((2 * ξ * (1 - ξ) / Real.pi ^ 2) * Fintype.card ι)) := by
  let b : ℝ := (2 * ξ * (1 - ξ) / Real.pi ^ 2) * Fintype.card ι
  have hb : 0 < b := by
    have hcompl : 0 < 1 - ξ := by linarith
    have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
    dsimp [b]
    positivity
  let g (s : ℝ) := Real.exp (-b * s ^ 2)
  have hg : Integrable g := integrable_exp_neg_mul_sq hb
  have hπ : -Real.pi + 2 * Real.pi = Real.pi := by ring
  let f (t : PhaseCircle) := ‖countFourier q d t‖
  have hf : Continuous f := (continuous_countFourier q d).norm
  have hcmp (s : ℝ) (hs : s ∈ Set.Ioc (-Real.pi) Real.pi) : f (s : PhaseCircle) ≤ g s := by
    refine (norm_countFourier_le q d ξ hq s).trans (Real.exp_le_exp.mpr ?_)
    have hscale : 0 ≤ 2 * (Fintype.card ι : ℝ) * ξ * (1 - ξ) := by
      have : 0 ≤ 1 - ξ := by linarith
      positivity
    have h := mul_le_mul_of_nonneg_left (sin_half_sq_lower s hs) hscale
    dsimp [b]
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hfi : IntegrableOn (fun s : ℝ ↦ f (s : PhaseCircle)) (Set.Ioc (-Real.pi) Real.pi) := by
    exact hg.integrableOn.mono' ((hf.comp (AddCircle.continuous_mk' (2 * Real.pi))).aestronglyMeasurable) <| by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact ae_of_all _ (fun s hs ↦ by simpa [f] using hcmp s hs)
  have hnorm :
      (bernoulliProduct q).real (countAtom d) ≤ ∫ t, f t ∂AddCircle.haarAddCircle := by
    have h := norm_integral_le_integral_norm (μ := AddCircle.haarAddCircle) (f := countFourier q d)
    rw [← probability_countAtom_eq_integral q d, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg] at h
    exact h
  refine hnorm.trans ?_
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.integral_preimage _ (-Real.pi), hπ, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
  calc
    _ ≤ ∫ s in Set.Ioc (-Real.pi) Real.pi, g s :=
      setIntegral_mono_on hfi hg.integrableOn measurableSet_Ioc hcmp
    _ ≤ ∫ s, g s := setIntegral_le_integral hg (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))
    _ = _ := integral_gaussian b

/-- The uniform bound Cξ / sqrt(m + 1), including the empty family. -/
theorem probability_countAtom_le_inv_sqrt (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} [Fintype ι] (q : ι → Set.Icc (0 : ℝ) 1),
      (∀ i, ξ ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1 - ξ) → ∀ d : ℤ,
        (bernoulliProduct q).real (countAtom d) ≤ C / Real.sqrt ((Fintype.card ι : ℝ) + 1) := by
  let a : ℝ := 2 * ξ * (1 - ξ) / Real.pi ^ 2
  have ha : 0 < a := by
    have : 0 < 1 - ξ := by linarith
    dsimp [a]
    positivity
  let K : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / a)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨max 1 (K * Real.sqrt 2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro index _ q hq d
  let m := Fintype.card index
  change _ ≤ _ / Real.sqrt ((m : ℝ) + 1)
  by_cases hm : m = 0
  · simp [hm]
  have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hraw := probability_countAtom_le_gaussian q ξ hξ hξ' hq (Nat.pos_of_ne_zero hm) d
  change _ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / (a * (m : ℝ))) at hraw
  rw [← div_div, Real.sqrt_div (by positivity : 0 ≤ Real.pi / a), ← mul_div_assoc] at hraw
  have hsqrt : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt m := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hone : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm
    exact Real.sqrt_le_sqrt (by linarith)
  apply (le_div_iff₀ (Real.sqrt_pos_of_pos (by positivity))).mpr
  calc
    _ ≤ (K / Real.sqrt m) * (Real.sqrt 2 * Real.sqrt m) :=
      mul_le_mul hraw hsqrt (Real.sqrt_nonneg _) (div_nonneg hK (Real.sqrt_nonneg _))
    _ = K * Real.sqrt 2 := by field_simp [(Real.sqrt_pos_of_pos hm').ne']
    _ ≤ _ := le_max_right _ _

end BoundedEdgeRegularSubgraphs
