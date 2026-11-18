module

public import BoundedEdgeRegularSubgraphs.DensityIteration
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Parameter choices for the degree-variance extraction
-/

public section

open Filter Asymptotics

namespace BoundedEdgeRegularSubgraphs

/-- The scale in Theorem 5.3 leaves enough vertices for density
iteration and trimming. -/
theorem eventually_logarithmic_extraction_scale (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∀ᶠ n : ℕ in atTop,
      let L := Real.log n
      let η := Real.sqrt (32 / L)
      0 < L ∧ 0 < η ∧ η ≤ 1 / 16 ∧ 3 * Real.sqrt η ≤ a₀ ∧
        η ^ 2 = 32 / L ∧
        (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧
        (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ) *
          max 32 (8 * Real.log (16 / η ^ 2)) ≤ (n : ℝ) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hroot : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hcast
  have hsmall : ∀ᶠ n : ℕ in atTop, (4 : ℝ) * Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      hcast).bound (show 0 < (1 / 4 : ℝ) by norm_num)
    filter_upwards [h, hlog.eventually_ge_atTop 16] with n hn hL
    change ‖Real.log n‖ ≤ 1 / 4 * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ at hn
    rw [Real.norm_of_nonneg (show 0 ≤ Real.log n by linarith),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hn
    linarith only [hn]
  filter_upwards [hlog.eventually_ge_atTop 8192, hlog.eventually_ge_atTop
      (32 / ((a₀ / 3) ^ 2) ^ 2), hsmall, hroot.eventually_ge_atTop 32,
    eventually_ge_atTop (1 : ℕ)] with n hL hL₀ hSmall hRoot hn
  dsimp only
  let L := Real.log n
  let η := Real.sqrt (32 / L)
  have hL' : 0 < L := (by norm_num : (0 : ℝ) < 8192).trans_le hL
  have hη₀ : 0 < η := Real.sqrt_pos.mpr (div_pos (by norm_num) hL')
  have hη₂ : η ^ 2 = 32 / L := Real.sq_sqrt (by positivity)
  have hη₁ : η ≤ 1 / 16 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hL').2
    linarith only [hL]
  have hηa : 3 * Real.sqrt η ≤ a₀ := by
    have hq : 0 < ((a₀ / 3) ^ 2) ^ 2 := by positivity
    have hh := (div_le_iff₀ hq).1 hL₀
    have hηa' : η ≤ (a₀ / 3) ^ 2 :=
      Real.sqrt_le_iff.mpr ⟨sq_nonneg _, (div_le_iff₀ hL').2 (by simpa only [mul_comm] using hh)⟩
    have h := Real.sqrt_le_iff.mpr ⟨show 0 ≤ a₀ / 3 by positivity, hηa'⟩
    linarith only [h]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans_le hn'
  have harg : 2 / η ^ 2 = L / 16 := by rw [hη₂]; field_simp <;> ring
  have hJ' : (⌈2 / η ^ 2⌉₊ : ℝ) ≤ L / 16 + 1 := by
    rw [harg]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith only [h]
  have hPower : (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 4) _),
      ← Real.exp_log (Real.rpow_pos_of_pos hn₀ _), Real.log_pow, Real.log_rpow hn₀]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (L / 16 + 1) * 2 := mul_le_mul hJ' hlog4 (Real.log_nonneg (by norm_num)) (by positivity)
      _ ≤ _ := by linarith only [hL]
  have hArg : 16 / η ^ 2 = L / 2 := by rw [hη₂]; field_simp <;> ring
  have hM : max 32 (8 * Real.log (16 / η ^ 2)) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    apply max_le hRoot
    rw [hArg]
    have h := Real.log_le_sub_one_of_pos (show 0 < L / 2 by positivity)
    exact (show 8 * Real.log (L / 2) ≤ 4 * L by linarith only [h]).trans hSmall
  refine ⟨hL', hη₀, hη₁, hηa, hη₂, hPower, ?_⟩
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
      mul_le_mul hPower hM (by positivity) (by positivity)
    _ = (n : ℝ) ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hn₀]; norm_num
    _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
    _ = n := Real.rpow_one _

/-- The even order chosen at the logarithmic scale. -/
noncomputable def logarithmicEvenOrder (a : ℝ) (n : ℕ) : ℕ :=
  2 * ⌊a * Real.log n ^ 2 / 2⌋₊

theorem eventually_logarithmicEvenOrder_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      a / 2 * Real.log n ^ 2 ≤ (logarithmicEvenOrder a n : ℝ) ∧
        (logarithmicEvenOrder a n : ℝ) ≤ a * Real.log n ^ 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (max 1 (4 / a))] with n hn
  let L := Real.log n
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hn
  have hL : 4 / a ≤ L := (le_max_right _ _).trans hn
  have h₁ : 4 ≤ a * L := by rw [mul_comm]; exact (div_le_iff₀ ha).1 hL
  have h₂ : 4 ≤ a * L ^ 2 := by nlinarith only [h₁, mul_nonneg ha.le (mul_nonneg (sub_nonneg.mpr hL₁) (show 0 ≤ L by linarith only [hL₁]))]
  change a / 2 * L ^ 2 ≤ ((2 * ⌊a * L ^ 2 / 2⌋₊ : ℕ) : ℝ) ∧
    ((2 * ⌊a * L ^ 2 / 2⌋₊ : ℕ) : ℝ) ≤ a * L ^ 2
  push_cast
  exact ⟨by linarith only [Nat.lt_floor_add_one (a * L ^ 2 / 2), h₂],
    by linarith only [Nat.floor_le (show 0 ≤ a * L ^ 2 / 2 by positivity)]⟩

end BoundedEdgeRegularSubgraphs
