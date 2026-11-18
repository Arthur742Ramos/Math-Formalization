module

public import BoundedEdgeRegularSubgraphs.FourierTailRates
import Mathlib.Tactic

/-!
# Integer cutoffs for the Fourier exterior argument
-/

@[expose] public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- The cutoff for the number of bad edges. -/
noncomputable def fourierBadCutoff (k : ℕ) : ℕ := ⌈(k : ℝ) * Real.log k ^ 2⌉₊

/-- A common bound for the number of exceptional coordinates when the
fraction of vertices outside the deleted clique is at least `τ`. -/
noncomputable def fourierExceptionCutoff (τ : ℝ) (k : ℕ) : ℕ :=
  ⌈(4 / τ) * (Real.log k ^ 2 + 1)⌉₊

theorem fourierExceptionCutoff_le (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    (fourierExceptionCutoff τ k : ℝ) ≤ (4 / τ) * Real.log k ^ 2 + (4 / τ + 1) := by
  unfold fourierExceptionCutoff
  have h := Nat.ceil_lt_add_one (show 0 ≤ (4 / τ) * (Real.log k ^ 2 + 1) by positivity)
  linarith only [h]

private theorem tendsto_log_sq_div_nat :
    Tendsto (fun k : ℕ ↦ Real.log k ^ 2 / (k : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 2 zero_lt_one).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop)
  change Tendsto (fun k : ℕ ↦ Real.log k ^ (2 : ℝ) / (k : ℝ) ^ (1 : ℝ)) atTop (𝓝 0) at h
  simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one] using h

theorem tendsto_exceptionCutoff_div_nat {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun k : ℕ ↦ (fourierExceptionCutoff τ k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun k : ℕ ↦ (4 / τ) * (Real.log k ^ 2 / (k : ℝ)) +
      (4 / τ + 1) * (k : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds (x := 4 / τ)).mul tendsto_log_sq_div_nat).add
        ((tendsto_const_nhds (x := 4 / τ + 1)).mul hi)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall (fun _ ↦ by positivity)
  · exact Eventually.of_forall (fun k ↦ by
      have h := div_le_div_of_nonneg_right (fourierExceptionCutoff_le k hτ) (Nat.cast_nonneg k)
      rwa [add_div, mul_div_assoc, div_eq_mul_inv (4 / τ + 1)] at h)

theorem tendsto_badCutoff_div_nat_sq :
    Tendsto (fun k : ℕ ↦ (fourierBadCutoff k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 0) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun k : ℕ ↦ Real.log k ^ 2 / (k : ℝ) + ((k : ℝ)⁻¹) ^ 2) atTop (𝓝 0) :=
    by simpa using tendsto_log_sq_div_nat.add (hi.pow 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall (fun _ ↦ by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have h := div_le_div_of_nonneg_right
      (Nat.ceil_lt_add_one (show 0 ≤ (k : ℝ) * Real.log k ^ 2 by positivity)).le
      (sq_nonneg (k : ℝ))
    refine h.trans_eq ?_
    field_simp [hk₀.ne']

/-- The integer cutoffs satisfy the covering and replacement inequalities
uniformly over all admissible sizes of the undeleted set. -/
theorem eventually_valid_fourier_cutoffs {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      let M := fourierBadCutoff k
      let L := fourierExceptionCutoff τ k
      (L : ℝ) / (k : ℝ) ^ 2 ≤ η / 2 ∧
      ∀ m : ℕ, τ * k ≤ m → m ≤ k → 3 ≤ m ∧ 2 * M ≤ m * L ∧
        2 * M < (m - (L + 1)) * (m - (L + 1) - 1) ∧ τ * k / 2 ≤ ((m - L : ℕ) : ℝ) := by
  let M := fourierBadCutoff
  let L := fourierExceptionCutoff τ
  have hkInf : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hkInf.eventually_ge_atTop (8 / τ),
    (tendsto_exceptionCutoff_div_nat hτ).eventually_lt_const (show 0 < τ / 4 by positivity),
    (tendsto_exceptionCutoff_div_nat hτ).eventually_lt_const (show 0 < η / 2 by positivity),
    tendsto_badCutoff_div_nat_sq.eventually_lt_const (show 0 < τ ^ 2 / 8 by positivity)] with
    k hk hlarge hL hwin hM
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlarge' : (8 : ℝ) ≤ τ * k := by simpa only [mul_comm] using (div_le_iff₀ hτ).mp hlarge
  have hL' : (L k : ℝ) < τ * k / 4 := by
    have h := (div_lt_iff₀ hk₀).mp hL
    linarith only [h]
  have hM' : 2 * (M k : ℝ) < (τ * k / 2) ^ 2 := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hk₀)).mp hM
    nlinarith only [h]
  refine ⟨?_, ?_⟩
  · refine (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk₀ ?_).trans hwin.le
    have h := mul_le_mul_of_nonneg_left hk₁ hk₀.le
    linarith only [h]
  · intro m hm _
    have hm3 : 3 ≤ m := by
      exact_mod_cast (show (3 : ℝ) ≤ m by linarith only [hm, hlarge'])
    have hMle : (M k : ℝ) ≤ (k : ℝ) * (Real.log k ^ 2 + 1) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ (k : ℝ) * Real.log k ^ 2 by positivity)
      change (M k : ℝ) < (k : ℝ) * Real.log k ^ 2 + 1 at h
      linarith only [h, hk₁]
    have hLle : (4 / τ) * (Real.log k ^ 2 + 1) ≤ L k := Nat.le_ceil _
    have h₀ : 0 ≤ (4 / τ) * (Real.log k ^ 2 + 1) := by positivity
    have hdeg := mul_le_mul hm hLle h₀ (Nat.cast_nonneg m)
    have hdeg' : 2 * (M k : ℝ) ≤ (m : ℝ) * (L k : ℝ) := by
      have h : (τ * k) * ((4 / τ) * (Real.log k ^ 2 + 1)) =
          4 * k * (Real.log k ^ 2 + 1) := by field_simp
      rw [h] at hdeg
      nlinarith only [hdeg, hMle, mul_nonneg hk₀.le (show 0 ≤ Real.log k ^ 2 + 1 by positivity)]
    have hc : L k + 2 ≤ m := by
      have h : (L k : ℝ) + 2 ≤ m := by linarith only [hm, hL', hlarge']
      exact_mod_cast h
    have hq1 : τ * k / 2 ≤ ((m - (L k + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show L k + 1 ≤ m by omega), Nat.cast_add, Nat.cast_one]
      linarith only [hm, hL', hlarge']
    have hq2 : τ * k / 2 ≤ ((m - (L k + 1) - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ m - (L k + 1) by omega),
        Nat.cast_sub (show L k + 1 ≤ m by omega), Nat.cast_add, Nat.cast_one]
      linarith only [hm, hL', hlarge']
    have hq := mul_le_mul hq1 hq2 (show 0 ≤ τ * k / 2 by positivity) (Nat.cast_nonneg _)
    refine ⟨hm3, by exact_mod_cast hdeg', ?_, ?_⟩
    · have h := hM'.trans_le ((pow_two _).trans_le hq)
      exact_mod_cast h
    · exact hq1.trans (by exact_mod_cast Nat.sub_le_sub_left (Nat.le_succ (L k)) m)

end BoundedEdgeRegularSubgraphs
