module

public import BoundedEdgeRegularSubgraphs.GaussianQuarticBoxError
public import BoundedEdgeRegularSubgraphs.GaussianQuarticImageMoment
public import BoundedEdgeRegularSubgraphs.GaussianQuarticRates
public import BoundedEdgeRegularSubgraphs.GaussianLinearTail
import Mathlib.Tactic

/-!
# Lemma A.3 with a uniform linear covariance scale
-/

public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators Topology

namespace BoundedEdgeRegularSubgraphs

private theorem abs_exp_sub_le_of_abs_le {m ν M : ℝ} (hm : |m| ≤ M) (hν : |ν| ≤ M) :
    |Real.exp m - Real.exp ν| ≤ Real.exp M * |m - ν| := by
  have h := (convex_Icc (-M) M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr hx.2)
    (abs_le.mp hν) (abs_le.mp hm)
  simpa only [Real.norm_eq_abs] using h

/-- The quartic correction has uniformly bounded mean, and its weight
truncated to the shrinking box converges in L¹ to the exponential of
that mean. The two matrix bounds hold for the full and residual arrays. -/
theorem eventually_gaussian_quartic_box_weight_sub_le {a K : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ)
        (B : Matrix (Fin n) (Fin n) ℝ),
        (∀ e ∈ A, |b e| ≤ K) →
        (∀ i, (∑ j, (B i j) ^ 2) ≤ a / n) →
        (∀ x : Fin n → ℝ, (∑ i, (B *ᵥ x) i ^ 2) ≤ (a / n) * ∑ i, x i ^ 2) →
        let γ := standardGaussianProduct n
        let h := fun x ↦ edgeQuartic A b (B *ᵥ x)
        let U := {x : Fin n → ℝ | B *ᵥ x ∈ realPhaseBox (α := Fin n) (fourierBoxRadius n)}
        let ν := ∫ x, h x ∂γ
        |ν| ≤ M ∧ (∫ x, |U.indicator (fun x ↦ Real.exp (h x)) x - Real.exp ν| ∂γ) ≤ ε := by
  let W := 105 * K ^ 2 * (4 * a) ^ 4
  let M := Real.sqrt W + 24 * K * a ^ 2
  let L (n : ℕ) := (32 * K * Real.sqrt a) * (Real.log n ^ 3 / Real.sqrt n)
  let t (n : ℕ) := 2 * (n : ℝ) * Real.exp (-(1 / (2 * a)) * Real.log n ^ 2)
  let p (n : ℕ) := 2 * (n : ℝ) ^ 3 * Real.exp (-(1 / (2 * a)) * Real.log n ^ 2)
  let E (n : ℕ) := Real.sqrt (Real.exp (2 * M) * (Real.exp (2 * L n ^ 2) - 1)) +
    Real.exp M * ((K + 1 / 2) * p n + W / (2 * (n : ℝ))) + Real.exp M * t n
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro ε hε
  have hc : 0 < 1 / (2 * a) := by positivity
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop (𝓝 0) := by
    simpa only [L, mul_zero] using tendsto_const_nhds.mul tendsto_log_cube_div_sqrt_nat
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa only [t, ← mul_assoc, pow_one, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_nat_pow_mul_exp_neg_log_sq 1 hc)
  have hp : Tendsto p atTop (𝓝 0) := by
    simpa only [p, ← mul_assoc, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_nat_pow_mul_exp_neg_log_sq 3 hc)
  have hInv : Tendsto (fun n : ℕ ↦ W / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := W / 2)).mul (tendsto_inv_atTop_zero.comp hnat)
    simpa only [Function.comp_apply, div_div, div_eq_mul_inv, mul_inv, mul_assoc, mul_comm,
      mul_left_comm, mul_zero, zero_mul] using h
  have hL' : Tendsto (fun n ↦ 2 * L n ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul (hL.pow 2)
  have hE₁ : Tendsto (fun n ↦ Real.sqrt (Real.exp (2 * M) * (Real.exp (2 * L n ^ 2) - 1)))
      atTop (𝓝 0) := by
    have hexp := (Real.continuous_exp.continuousAt (x := (0 : ℝ))).tendsto.comp hL'
    have h := (tendsto_const_nhds (x := Real.exp (2 * M))).mul
      (hexp.sub (tendsto_const_nhds (x := (1 : ℝ))))
    have hh : Tendsto (fun n ↦ Real.exp (2 * M) * (Real.exp (2 * L n ^ 2) - 1))
        atTop (𝓝 0) := by simpa using h
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.comp hh
  have hE₂ : Tendsto (fun n ↦ Real.exp M * ((K + 1 / 2) * p n + W / (2 * (n : ℝ))))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := Real.exp M)).mul
      (((tendsto_const_nhds (x := K + 1 / 2)).mul hp).add hInv)
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, mul_zero, add_zero] using
      (hE₁.add hE₂).add ((tendsto_const_nhds (x := Real.exp M)).mul ht)
  filter_upwards [hE.eventually_lt_const hε, eventually_ge_atTop (1 : ℕ),
    fourierBoxRadius_tendsto_zero.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)] with
    n hE' hn hr'
  intro A b B hb hB hB'
  let γ := standardGaussianProduct n
  let r := fourierBoxRadius n
  let h (x : Fin n → ℝ) := edgeQuartic A b (B *ᵥ x)
  let H (x : Fin n → ℝ) := edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))
  let U := {x : Fin n → ℝ | B *ᵥ x ∈ realPhaseBox (α := Fin n) r}
  let ν := ∫ x, h x ∂γ
  let m := ∫ x, H x ∂γ
  let D := a / (n : ℝ)
  let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * Real.sqrt D
  have hn₀ : 0 < n := by omega
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn₀
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < D := div_pos ha hnℝ
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg hn₁) (Real.sqrt_nonneg _)
  have hcard : (A.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h := Fintype.card_le_of_injective (fun e : Edge (Fin n) ↦ e.val) Subtype.val_injective
    rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h
    have hc' := (Finset.card_le_univ A).trans h
    exact_mod_cast hc'
  obtain ⟨hh, hh₂, htwo, hmean⟩ := gaussian_edgeQuartic_image_moments A b hK hD.le hb B hB
  have htwo' : 105 * (A.card : ℝ) ^ 2 * K ^ 2 * (4 * D) ^ 4 ≤ W := by
    calc
      _ ≤ 105 * ((n : ℝ) ^ 2) ^ 2 * K ^ 2 * (4 * D) ^ 4 := by gcongr
      _ = W := by dsimp only [D, W]; field_simp [hnℝ.ne'] <;> ring
  have hν : |ν| ≤ M :=
    (hmean.trans (Real.sqrt_le_sqrt htwo')).trans
      (le_add_of_nonneg_right (by positivity))
  have hm₀ : |m| ≤ 24 * K * ((n : ℝ) - 1) * n * D ^ 2 := by
    change |∫ x, H x ∂γ| ≤ _
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (by
      simp only [Real.norm_eq_abs]
      exact integral_abs_clipped_edgeQuartic_le hn₀ A b hK hr hb B hB)
  have hm : |m| ≤ M := by
    refine hm₀.trans ?_
    calc
      _ ≤ 24 * K * (n : ℝ) * n * D ^ 2 := by gcongr; exact sub_le_self _ zero_le_one
      _ = 24 * K * a ^ 2 := by dsimp only [D]; field_simp [hnℝ.ne'] <;> ring
      _ ≤ M := le_add_of_nonneg_left (Real.sqrt_nonneg W)
  refine ⟨hν, ?_⟩
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |(B *ᵥ x) i| ≤ r} by ext x; simp [U, realPhaseBox]]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    change Measurable (fun x : Fin n → ℝ ↦ |∑ j, B i j * x j|)
    have hm' : Measurable (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j) :=
      Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul (measurable_pi_apply j))
    exact continuous_abs.measurable.comp hm'
  have htail : γ.real Uᶜ ≤ t n := by
    refine (probability_gaussian_mulVec_outside_box_le B hD hB hr).trans_eq ?_
    have he : r ^ 2 / (2 * D) = (1 / (2 * a)) * Real.log n ^ 2 := by
      dsimp only [r, D, fourierBoxRadius]
      rw [div_pow, Real.sq_sqrt hnℝ.le]
      field_simp [hnℝ.ne', ha.ne'] <;> ring
    dsimp only [t]
    rw [show -r ^ 2 / (2 * D) = -(1 / (2 * a)) * Real.log n ^ 2 by
      calc
        _ = -(r ^ 2 / (2 * D)) := by ring
        _ = _ := by rw [he]; ring]
  let R := (A.card : ℝ) * (K * (2 * r) ^ 4)
  have hR : ∀ x, |H x| ≤ R := fun x ↦ abs_edgeQuartic_clip_le A b hK hr hb (B *ᵥ x)
  have hContB (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ (B *ᵥ x) i) := by
    change Continuous (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j)
    exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_apply j))
  have hContH : Continuous H := by
    unfold H edgeQuartic clipRadius
    apply continuous_finsetSum
    intro e _
    have hc' (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ min r (max (-r) ((B *ᵥ x) i))) :=
      continuous_const.min (continuous_const.max (hContB i))
    exact continuous_const.mul (((hc' e.val.1).add (hc' e.val.2)).pow 4)
  have hint : Integrable H γ := Integrable.of_bound hContH.aestronglyMeasurable R
    (ae_of_all _ (fun x ↦ by rw [Real.norm_eq_abs]; exact hR x))
  have heq (x : Fin n → ℝ) (hx : x ∈ U) : h x = H x := by
    unfold h H
    rw [show (fun i ↦ clipRadius r ((B *ᵥ x) i)) = B *ᵥ x from
      funext (fun i ↦ clipRadius_eq_of_abs_le (hx i))]
  have hdiff := abs_integral_sub_le_of_eq_on U hU h H hh hint heq hR
    (s := (n : ℝ)) hnℝ hh₂
  have hR' : R + (n : ℝ) / 2 ≤ (K + 1 / 2) * (n : ℝ) ^ 2 := by
    have hs := pow_le_pow_left₀ (show 0 ≤ 2 * r by positivity)
      (show 2 * r ≤ 1 by linarith only [hr']) 4
    have hR₀ : R ≤ K * (n : ℝ) ^ 2 := by
      dsimp only [R]
      calc
        _ ≤ (n : ℝ) ^ 2 * (K * (1 : ℝ) ^ 4) := by gcongr
        _ = _ := by ring
    nlinarith only [hR₀, mul_le_mul_of_nonneg_right hn₁ hnℝ.le]
  have hdiff' : |m - ν| ≤ (K + 1 / 2) * p n + W / (2 * (n : ℝ)) := by
    refine hdiff.trans ?_
    have hp' : (n : ℝ) ^ 2 * t n = p n := by dsimp only [t, p]; ring
    calc
      _ ≤ ((K + 1 / 2) * (n : ℝ) ^ 2) * t n + W / (2 * (n : ℝ)) :=
        add_le_add (mul_le_mul hR' htail ENNReal.toReal_nonneg (by positivity))
          (div_le_div_of_nonneg_right (htwo.trans htwo') (by positivity))
      _ = _ := by rw [mul_assoc, hp']
  have hκ₀ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hκ : κ ≤ L n := quartic_box_lipschitzRate_le hn₀ hK ha
  have hs := integral_abs_quartic_box_weight_sub_le hn₀ A b hK hr (Real.sqrt_nonneg D) hb B
    (fun x ↦ by rw [Real.sq_sqrt hD.le]; exact hB' x)
  refine (hs.trans ?_).trans hE'.le
  dsimp only [E]
  apply add_le_add (add_le_add ?_ ?_) ?_
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      linarith only [(le_abs_self m).trans hm]
    · apply sub_le_sub_right
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ₀ hκ 2) (by norm_num))
    · exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
    · positivity
  · exact (abs_exp_sub_le_of_abs_le hm hν).trans (mul_le_mul_of_nonneg_left hdiff' (Real.exp_nonneg _))
  · exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self ν).trans hν)) htail ENNReal.toReal_nonneg
      (Real.exp_nonneg _)

end BoundedEdgeRegularSubgraphs
