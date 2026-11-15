/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.PhaseAlias
public import ErdosOverlap.Gram.Covariance

/-!
# Exact tent-lag identity for phase-averaged physical cells

The tent has height one. All convolution identities below are proved for
Lebesgue integrals; finite covariance entries are exact phase averages.
-/

open MeasureTheory Set
open scoped Convolution

namespace ErdosOverlap.Gram

public section
noncomputable section

@[expose] def tent (a t : ℝ) : ℝ := max (1 - |t| / a) 0

@[expose] def contrastAutocorrelation (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, contrast h x * contrast h (x + t)

@[expose] def phaseWindow (a : ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) a).indicator (fun _ => (1 : ℝ))

@[expose] def smoothedContrast (h : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  contrast h ⋆[ContinuousLinearMap.mul ℝ ℝ] phaseWindow a

theorem real_convolution_comm (f g : ℝ → ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) =
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ] f) := by
  funext x
  rw [convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

theorem real_convolution_reflection (f g : ℝ → ℝ) (x : ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) (-x) =
      ((fun t => f (-t)) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun t => g (-t))) x := by
  change (∫ t : ℝ, f t * g (-x - t)) = ∫ t : ℝ, f (-t) * g (-(x - t))
  have hi := integral_neg_eq_self (fun t : ℝ => f t * g (-x - t)) volume
  calc
    _ = ∫ t : ℝ, f (-t) * g (-x - (-t)) := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [show -x - (-t) = -(x - t) by ring]

theorem real_convolution_exists_of_bounded {f g : ℝ → ℝ} {C : ℝ}
    (hf : Integrable f) (hg : Measurable g) (hgb : ∀ x, |g x| ≤ C) (x : ℝ) :
    ConvolutionExistsAt f g x (ContinuousLinearMap.mul ℝ ℝ) volume := by
  have hi : Integrable (fun t : ℝ => g (x - t) * f t) := by
    apply hf.bdd_mul (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, id_eq] using hgb (x - t))
  change Integrable (fun t : ℝ => f t * g (x - t))
  exact hi.congr (Filter.Eventually.of_forall (fun t => mul_comm _ _))

/-- Boundedness of the third factor supplies the actual Fubini condition. -/
theorem real_convolution_assoc_of_bounded {f g k : ℝ → ℝ} {C : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hk : Measurable k)
    (hkb : ∀ x, |k x| ≤ C) (x : ℝ) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x := by
  have hbase : Integrable (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2))
      (volume.prod volume) := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  have hi : Integrable (fun p : ℝ × ℝ => f p.2 * (g (p.1 - p.2) * k (x - p.1)))
      (volume.prod volume) := by
    have hw : Integrable (fun p : ℝ × ℝ => k (x - p.1) * (f p.2 * g (p.1 - p.2)))
        (volume.prod volume) := by
      apply hbase.bdd_mul (hk.comp (measurable_const.sub measurable_fst)).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply] using hkb (x - p.1))
    exact hw.congr (Filter.Eventually.of_forall (fun p => by ring))
  apply convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
  · intro u v w
    exact mul_assoc _ _ _
  · exact hf.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hg
  · exact Filter.Eventually.of_forall (real_convolution_exists_of_bounded hg hk hkb)
  · exact hi

theorem real_convolution_four_swap {f g h k : ℝ → ℝ} {B C D : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hgm : Measurable g) (hhm : Measurable h) (hkm : Measurable k)
    (hgb : ∀ x, |g x| ≤ B) (hhb : ∀ x, |h x| ≤ C) (hkb : ∀ x, |k x| ≤ D)
    (x : ℝ) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (h ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x =
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x := by
  have hfg := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg
  have hfh := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hh
  have hswap : ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] h) =
      ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) ⋆[ContinuousLinearMap.mul ℝ ℝ] g) := by
    funext t
    rw [real_convolution_assoc_of_bounded hf hg hhm hhb,
      real_convolution_comm g h,
      ← real_convolution_assoc_of_bounded hf hh hgm hgb]
  rw [← real_convolution_assoc_of_bounded hfg hh hkm hkb, hswap,
    real_convolution_assoc_of_bounded hfh hg hkm hkb]

theorem phaseWindow_measurable (a : ℝ) : Measurable (phaseWindow a) :=
  measurable_const.indicator measurableSet_Icc

theorem phaseWindow_integrable (a : ℝ) : Integrable (phaseWindow a) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact integrableOn_const (measure_Icc_lt_top.ne)

theorem phaseWindow_abs_le_one (a x : ℝ) : |phaseWindow a x| ≤ 1 := by
  by_cases hx : x ∈ Icc (0 : ℝ) a <;> simp [phaseWindow, hx]

theorem phaseWindow_autocorrelation (a t : ℝ) :
    (∫ x : ℝ, phaseWindow a x * phaseWindow a (x + t)) = max (a - |t|) 0 := by
  have hfun : (fun x => phaseWindow a x * phaseWindow a (x + t)) =
      (Icc (max 0 (-t)) (min a (a - t))).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : ℝ) a
    · by_cases hxt : x + t ∈ Icc (0 : ℝ) a
      · have hboth : x ∈ Icc (max 0 (-t)) (min a (a - t)) :=
          ⟨max_le hx.1 (by linarith [hxt.1]), le_min hx.2 (by linarith [hxt.2])⟩
        simp [phaseWindow, hx, hxt, hboth]
      · have hnot : x ∉ Icc (max 0 (-t)) (min a (a - t)) := by
          intro hboth
          exact hxt ⟨by linarith [le_of_max_le_right hboth.1],
            by linarith [le_of_le_min_right hboth.2]⟩
        simp [phaseWindow, hx, hxt, hnot]
    · have hnot : x ∉ Icc (max 0 (-t)) (min a (a - t)) := by
        intro hboth
        exact hx ⟨le_of_max_le_left hboth.1, le_of_le_min_left hboth.2⟩
      simp [phaseWindow, hx, hnot]
  rw [hfun, integral_indicator_const (1 : ℝ) measurableSet_Icc,
    smul_eq_mul, mul_one, Real.volume_real_Icc]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, max_eq_left (by linarith : -t ≤ 0),
      min_eq_right (by linarith : a - t ≤ a), sub_zero]
  · rw [abs_of_nonpos ht, max_eq_right (by linarith : 0 ≤ -t),
      min_eq_left (by linarith : a ≤ a - t)]

theorem tent_even (a t : ℝ) : tent a (-t) = tent a t := by simp [tent]

theorem tent_mul_scale {a : ℝ} (ha : 0 < a) (t : ℝ) :
    a * tent a t = max (a - |t|) 0 := by
  unfold tent
  rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
  congr 1
  field_simp

theorem correlation_eq_reflected_convolution (f g : ℝ → ℝ) (t : ℝ) :
    (∫ x : ℝ, f x * g (x + t)) =
      ((fun x => f (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ] g) t := by
  change (∫ x : ℝ, f x * g (x + t)) = ∫ x : ℝ, f (-x) * g (t - x)
  simpa only [sub_eq_add_neg, add_comm] using
    (integral_neg_eq_self (fun x : ℝ => f x * g (x + t)) volume).symm

theorem contrastAutocorrelation_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (contrastAutocorrelation h) := by
  have hi := (contrast_integrable hh).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (contrast_integrable hh)
  exact hi.congr (Filter.Eventually.of_forall (fun t =>
    (correlation_eq_reflected_convolution (contrast h) (contrast h) t).symm))

theorem smoothedContrast_autocorrelation {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ x : ℝ, smoothedContrast h a x * smoothedContrast h a (x + z)) =
      a * ∫ t : ℝ, contrastAutocorrelation h t * tent a (t - z) := by
  have hrev : (fun x => smoothedContrast h a (-x)) =
      ((fun x => contrast h (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (fun x => phaseWindow a (-x))) := by
    funext x
    exact real_convolution_reflection (contrast h) (phaseWindow a) x
  have hR : ((fun x => contrast h (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ] contrast h) =
      contrastAutocorrelation h := by
    funext t
    exact (correlation_eq_reflected_convolution (contrast h) (contrast h) t).symm
  have hT : ((fun x => phaseWindow a (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ] phaseWindow a) =
      fun t => a * tent a t := by
    funext t
    rw [← correlation_eq_reflected_convolution, phaseWindow_autocorrelation,
      tent_mul_scale ha]
  calc
    _ = ((fun x => smoothedContrast h a (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        smoothedContrast h a) z :=
      correlation_eq_reflected_convolution (smoothedContrast h a) (smoothedContrast h a) z
    _ = (((fun x => contrast h (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ] contrast h)
        ⋆[ContinuousLinearMap.mul ℝ ℝ]
        ((fun x => phaseWindow a (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ] phaseWindow a)) z := by
      rw [hrev]
      exact real_convolution_four_swap
        (contrast_integrable hh).comp_neg (phaseWindow_integrable a).comp_neg
        (contrast_integrable hh) ((phaseWindow_measurable a).comp measurable_neg)
        (contrast_measurable hh) (phaseWindow_measurable a)
        (fun x => phaseWindow_abs_le_one a (-x)) (contrast_abs_le_one hh)
        (phaseWindow_abs_le_one a) z
    _ = _ := by
      rw [hR, hT]
      change (∫ t : ℝ, contrastAutocorrelation h t * (a * tent a (z - t))) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      have ht : tent a (z - t) = tent a (t - z) := by
        unfold tent
        rw [abs_sub_comm]
      rw [ht]
      ring

/-- The continuous moving integral is exactly the actual phase-cell average. -/
theorem smoothedContrast_shift {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    smoothedContrast h a (x + a) = a * cellAverage h a x 0 := by
  have hfun : (fun u => contrast h u * phaseWindow a (x + a - u)) =
      (Icc x (x + a)).indicator (contrast h) := by
    funext u
    have hm : x + a - u ∈ Icc (0 : ℝ) a ↔ u ∈ Icc x (x + a) := by
      constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
    by_cases hu : u ∈ Icc x (x + a)
    · simp [phaseWindow, hu, hm.mpr hu]
    · have hn : x + a - u ∉ Icc (0 : ℝ) a := fun ht => hu (hm.mp ht)
      simp [phaseWindow, hu, hn]
  change (∫ u : ℝ, contrast h u * phaseWindow a (x + a - u)) = _
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : x ≤ x + a),
    cellAverage_eq_integral hh a x 0]
  simp only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, zero_mul, one_mul, add_zero]
  field_simp

theorem smoothedContrast_correlation_eq_cellProduct {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ x : ℝ, smoothedContrast h a x * smoothedContrast h a (x + z)) =
      a ^ 2 * ∫ x : ℝ, cellAverage h a x 0 * cellAverage h a (x + z) 0 := by
  calc
    _ = ∫ x : ℝ, smoothedContrast h a (x + a) * smoothedContrast h a (x + a + z) :=
      (integral_add_right_eq_self
        (fun x : ℝ => smoothedContrast h a x * smoothedContrast h a (x + z)) a).symm
    _ = ∫ x : ℝ, a ^ 2 * (cellAverage h a x 0 * cellAverage h a (x + z) 0) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [smoothedContrast_shift hh ha x,
        show x + a + z = (x + z) + a by ring, smoothedContrast_shift hh ha (x + z)]
      ring
    _ = _ := integral_const_mul _ _

/-- Moving-average autocorrelation is exactly smoothing by the height-one tent. -/
theorem cellProduct_tent_identity {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    a * (∫ x : ℝ, cellAverage h a x 0 * cellAverage h a (x + z) 0) =
      ∫ t : ℝ, contrastAutocorrelation h t * tent a (t - z) := by
  have h₁ := smoothedContrast_autocorrelation hh ha z
  have h₂ := smoothedContrast_correlation_eq_cellProduct hh ha z
  rw [h₂] at h₁
  have hcancel : a * (a * ∫ x : ℝ,
      cellAverage h a x 0 * cellAverage h a (x + z) 0) =
      a * ∫ t : ℝ, contrastAutocorrelation h t * tent a (t - z) := by
    nlinarith [h₁]
  exact (mul_left_cancel₀ ha.ne') hcancel

theorem cellAverage_shift_index (h : ℝ → ℝ) (a s : ℝ) (i : ℕ) :
    cellAverage h a s i = cellAverage h a (s + (i : ℝ) * a) 0 := by
  simp only [cellAverage, Nat.cast_zero, Nat.zero_add, Nat.cast_one,
    zero_mul, one_mul, add_zero]
  have harg : s + (i + 1 : ℕ) * a = s + (i : ℝ) * a + a := by push_cast; ring
  rw [harg]

theorem cellAverage_zero_of_add_nonpos (h : ℝ → ℝ) {a x : ℝ}
    (ha : 0 ≤ a) (hx : x + a ≤ 0) : cellAverage h a x 0 = 0 := by
  have hx0 : x ≤ 0 := by linarith
  simp only [cellAverage, Nat.cast_zero, Nat.zero_add, Nat.cast_one,
    zero_mul, one_mul, add_zero, primitive_eq_zero_of_nonpos h hx,
    primitive_eq_zero_of_nonpos h hx0, sub_self, zero_div]

theorem cellAverage_zero_of_two_le {h : ℝ → ℝ} (hh : Admissible h)
    {a x : ℝ} (ha : 0 ≤ a) (hx : 2 ≤ x) : cellAverage h a x 0 = 0 := by
  have hx1 : 2 ≤ x + a := by linarith
  simp only [cellAverage, Nat.cast_zero, Nat.zero_add, Nat.cast_one,
    zero_mul, one_mul, add_zero, primitive_eq_zero_of_two_le hh hx,
    primitive_eq_zero_of_two_le hh hx1, sub_self, zero_div]

/-- Translation of the phase integral tiles adjacent ordinary intervals. -/
theorem sum_phase_integrals {F : ℝ → ℝ} (hF : Continuous F) (M : ℕ) (a : ℝ) :
    (∑ i ∈ Finset.range (M + 1), ∫ s in -a..(0 : ℝ), F (s + (i : ℝ) * a)) =
      ∫ x in -a..((M : ℝ) * a), F x := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hshift : (∫ s in -a..(0 : ℝ), F (s + (M + 1 : ℕ) * a)) =
        ∫ x in ((M : ℝ) * a)..((M + 1 : ℕ) * a), F x := by
      have hc := intervalIntegral.integral_comp_add_right F
        (a := -a) (b := 0) ((M + 1 : ℕ) * a)
      have hl : -a + (M + 1 : ℕ) * a = (M : ℝ) * a := by push_cast; ring
      rw [hl, zero_add] at hc
      convert! hc using 1
    rw [hshift]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

theorem lag_product_zero_off_support {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 ≤ a) {N k : ℕ} (hk : k ≤ N)
    (hNa : (N : ℝ) * a = 2) (x : ℝ)
    (hx : x ∉ Icc (-a) ((N - k : ℕ) * a)) :
    cellAverage h a x 0 * cellAverage h a (x + (k : ℝ) * a) 0 = 0 := by
  by_cases hleft : -a ≤ x
  · have hright : (N - k : ℕ) * a < x := by
      by_contra! hh'
      exact hx ⟨hleft, hh'⟩
    have htwo : 2 ≤ x + (k : ℝ) * a := by
      rw [Nat.cast_sub hk] at hright
      nlinarith [hNa]
    rw [cellAverage_zero_of_two_le hh ha htwo, mul_zero]
  · have hzero := cellAverage_zero_of_add_nonpos h ha (x := x) (by linarith)
    rw [hzero, zero_mul]

theorem lag_product_integral_restrict {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 ≤ a) {N k : ℕ} (hk : k ≤ N) (hNa : (N : ℝ) * a = 2) :
    (∫ x : ℝ, cellAverage h a x 0 * cellAverage h a (x + (k : ℝ) * a) 0) =
      ∫ x in -a..((N - k : ℕ) * a),
        cellAverage h a x 0 * cellAverage h a (x + (k : ℝ) * a) 0 := by
  have hout := lag_product_zero_off_support hh ha hk hNa
  have hab : -a ≤ (N - k : ℕ) * a := by
    have hp := mul_nonneg (Nat.cast_nonneg (N - k) : (0 : ℝ) ≤ (N - k : ℕ)) ha
    linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- The exact finite covariance-to-tent identity, including both endpoint lags. -/
theorem covariance_tent_identity {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) {N k : ℕ} (hk : k ≤ N) (hNa : (N : ℝ) * a = 2) :
    a ^ 2 * (∑ i ∈ Finset.range (N - k + 1), covariance h a i (i + k)) =
      ∫ t : ℝ, contrastAutocorrelation h t * tent a (t - (k : ℝ) * a) := by
  let F : ℝ → ℝ := fun x => cellAverage h a x 0 * cellAverage h a (x + (k : ℝ) * a) 0
  have hF : Continuous F :=
    (cellAverage_continuous hh a 0).mul
      ((cellAverage_continuous hh a 0).comp (continuous_id.add continuous_const))
  have htile : (∑ i ∈ Finset.range (N - k + 1),
      ∫ s in -a..(0 : ℝ), cellAverage h a s i * cellAverage h a s (i + k)) =
      ∫ x in -a..((N - k : ℕ) * a), F x := by
    calc
      _ = ∑ i ∈ Finset.range (N - k + 1), ∫ s in -a..(0 : ℝ), F (s + (i : ℝ) * a) := by
        apply Finset.sum_congr rfl
        intro i _
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [F]
        rw [cellAverage_shift_index h a s i, cellAverage_shift_index h a s (i + k)]
        congr 2
        push_cast
        ring
      _ = _ := sum_phase_integrals hF (N - k) a
  calc
    _ = a * (∑ i ∈ Finset.range (N - k + 1),
        ∫ s in -a..(0 : ℝ), cellAverage h a s i * cellAverage h a s (i + k)) := by
      simp only [covariance, ← Finset.sum_div]
      field_simp
    _ = a * (∫ x in -a..((N - k : ℕ) * a), F x) := by rw [htile]
    _ = a * (∫ x : ℝ, F x) := by
      rw [← lag_product_integral_restrict hh ha.le hk hNa]
    _ = _ := cellProduct_tent_identity hh ha ((k : ℝ) * a)

end
end
end ErdosOverlap.Gram
