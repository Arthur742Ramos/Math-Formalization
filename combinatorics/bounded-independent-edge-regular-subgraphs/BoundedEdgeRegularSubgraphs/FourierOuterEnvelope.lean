module

public import BoundedEdgeRegularSubgraphs.FourierCutoffs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# A uniform rate for the exceptional-coordinate cover
-/

public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- The uniform upper bound obtained from the cardinality of the
exceptional-coordinate cover. -/
@[expose] noncomputable def fourierOuterEnvelope (η γ τ : ℝ) (L k : ℕ) : ℝ :=
  (4 * Real.pi / η) * ((k : ℝ) * (Real.pi * (k : ℝ) ^ 3) ^ L * Real.exp (-(γ * τ / 2) * k))

theorem fourier_outer_factor_le_envelope (k L m : ℕ) (hk : 0 < k) (hL : L ≤ k)
    {η γ τ : ℝ} (hη : 0 < η) (hγ : 0 ≤ γ)
    (hcount : τ * k / 2 ≤ ((m - L : ℕ) : ℝ))
    (hwin : (L : ℝ) / (k : ℝ) ^ 2 ≤ η / 2) :
    let u := ((k : ℝ) ^ 2)⁻¹
    (2 * k * (k.choose (k - L)) : ℕ) *
      (Real.exp (-γ * (m - L : ℕ)) * (Real.pi / u) ^ L / ((η - L * u) / Real.pi)) ≤
      fourierOuterEnvelope η γ τ L k := by
  let s : ℝ := k
  let u := (s ^ 2)⁻¹
  let f := Real.exp (-γ * (m - L : ℕ))
  let F := Real.exp (-(γ * τ / 2) * k)
  let p := η - (L : ℝ) * u
  have hs : 0 < s := by change (0 : ℝ) < k; exact_mod_cast hk
  have hp : η / 2 ≤ p := by
    dsimp only [p, u, s]
    rw [← div_eq_mul_inv]
    linarith only [hwin]
  have hp₀ : 0 < p := (by positivity : 0 < η / 2).trans_le hp
  have hf : f ≤ F := by
    have h := mul_le_mul_of_nonpos_left hcount (neg_nonpos.mpr hγ)
    apply Real.exp_le_exp.mpr
    linarith only [h]
  have hc : (k.choose (k - L) : ℝ) ≤ s ^ L := by
    rw [Nat.choose_symm hL]
    change (k.choose L : ℝ) ≤ (k : ℝ) ^ L
    exact_mod_cast Nat.choose_le_pow k L
  have hpow : Real.pi / u = Real.pi * s ^ 2 := by simp only [u, div_inv_eq_mul]
  have hrecip : (p / Real.pi)⁻¹ ≤ 2 * Real.pi / η := by
    rw [inv_div]
    apply (div_le_div_of_nonneg_left Real.pi_pos.le (by positivity : 0 < η / 2) hp).trans_eq
    ring
  change (2 * k * (k.choose (k - L)) : ℕ) *
    (f * (Real.pi / u) ^ L / (p / Real.pi)) ≤ _
  rw [hpow]
  push_cast
  rw [div_eq_mul_inv]
  have h₀ : 0 ≤ (Real.pi * s ^ 2) ^ L := by positivity
  have h₁ : 0 ≤ (p / Real.pi)⁻¹ := inv_nonneg.mpr (div_nonneg hp₀.le Real.pi_pos.le)
  have h₂ := mul_le_mul hf le_rfl h₀ (Real.exp_nonneg _)
  have h₃ := mul_le_mul h₂ hrecip h₁ (mul_nonneg (Real.exp_nonneg _) h₀)
  have h₄ := mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (2 : ℝ) * k))
    h₃ (by positivity) (by positivity)
  refine h₄.trans_eq ?_
  unfold fourierOuterEnvelope
  change 2 * s * s ^ L * (F * (Real.pi * s ^ 2) ^ L * (2 * Real.pi / η)) =
    (4 * Real.pi / η) * (s * (Real.pi * s ^ 3) ^ L * F)
  have he : s ^ L * (Real.pi * s ^ 2) ^ L = (Real.pi * s ^ 3) ^ L := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = (4 * Real.pi / η) * (s * (s ^ L * (Real.pi * s ^ 2) ^ L) * F) := by ring
    _ = _ := by rw [he]

/-- At the manuscript's cutoff the uniform exceptional-cover coefficient
tends to zero. -/
theorem tendsto_fourierOuterEnvelope {η γ τ : ℝ} (hη : 0 < η) (hγ : 0 < γ) (hτ : 0 < τ) :
    Tendsto (fun k ↦ fourierOuterEnvelope η γ τ (fourierExceptionCutoff τ k) k) atTop (𝓝 0) := by
  have h := tendsto_exceptional_cover_rate (fourierExceptionCutoff τ)
    (a := Real.pi) (c := γ * τ / 2) (D := 4 / τ) (E := 4 / τ + 1)
    Real.pi_pos (by positivity) (by positivity) (by positivity)
    (Eventually.of_forall (fun k ↦ fourierExceptionCutoff_le k hτ))
  unfold fourierOuterEnvelope
  simpa only [mul_zero] using (tendsto_const_nhds (x := 4 * Real.pi / η)).mul h

end BoundedEdgeRegularSubgraphs
