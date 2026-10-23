/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.NoiseUpper

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem core_witness_interval {m : ℕ} {ε δ : ℝ} {q : Fin m → ℝ} {u : ℝ}
    {B : Fin m → Fin m → ℝ} (fixed : Bool) (hw : UniformCoreWitness m ε δ q u B) :
    UniformIntervalWitness m ε δ fixed (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q (twoCore u)
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B := by
  norm_num only [Nat.cast_ofNat] at *
  rcases hw with ⟨hq,ha,_,hmass,hK,hB,hobsK,hobsD,hb,hresp⟩
  exact ⟨hq,ha,fun _ => rfl,hmass,hK,hB,hobsK,hobsD,hb,hresp⟩

theorem uniformMinimumCoreTotalSupport_sharp (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) (he1 : ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ ≤ 1) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) ≤
      (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ∧
    (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ≤
      (5 : ℕ)*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  refine ⟨uniformMinimumCoreTotalSupport_lower m hm ε δ hε hδ he,?_⟩
  obtain ⟨q,u,B,hw,hcount⟩ := uniform_core_uncertainty_upper m hm ε δ hε hδ he he1
  have hmin := uniformMinimumCoreTotalSupport_le m hm ε δ hε hδ q u B hw
  have hminR : (uniformMinimumCoreTotalSupport m hm ε δ hε hδ : ℝ) ≤ (supportSize q : ℝ)+2 :=
    by exact_mod_cast hmin
  exact le_trans hminR hcount

theorem uncertainty_rate_comparison (N e s : ℝ) (hN : 0 ≤ N) (he : 0 < e) (hs : 0 < s)
    (hcmp : (((3 : ℕ) : ℝ)/(8 : ℕ))*s ≤ e) :
    (5 : ℕ)*min N (1/Real.sqrt e) ≤ ((5 : ℕ)*Real.sqrt (((8 : ℕ) : ℝ)/(3 : ℕ)))*min N (1/Real.sqrt s) := by
  norm_num only [Nat.cast_ofNat] at *
  have hre : 0 < Real.sqrt e := Real.sqrt_pos.mpr he
  have hrs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hC : 1 ≤ Real.sqrt (8/3) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 8/3 by norm_num)
  have hC0 : 0 ≤ Real.sqrt (8/3) := Real.sqrt_nonneg _
  have hCsq : (Real.sqrt (8/3))^2=(8/3 : ℝ) := Real.sq_sqrt (by norm_num)
  have heq : (Real.sqrt (8/3)*Real.sqrt e)^2=(8/3 : ℝ)*e := by
    rw [mul_pow,hCsq,Real.sq_sqrt (le_of_lt he)]
  have hroots : Real.sqrt s ≤ Real.sqrt (8/3)*Real.sqrt e := by
    have hnn := mul_nonneg hC0 (le_of_lt hre)
    nlinarith [Real.sq_sqrt (le_of_lt hs)]
  have hfrac : 1/Real.sqrt e ≤ Real.sqrt (8/3)/Real.sqrt s :=
    (div_le_div_iff₀ hre hrs).mpr (by simpa only [one_mul] using hroots)
  rcases le_total N (1/Real.sqrt s) with hh | hh
  · rw [min_eq_left hh]
    calc
      _ ≤ 5*N := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ ≤ (5*Real.sqrt (8/3))*N := mul_le_mul_of_nonneg_right (by nlinarith) hN
  · rw [min_eq_right hh]
    calc
      _ ≤ 5*(1/Real.sqrt e) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ 5*(Real.sqrt (8/3)/Real.sqrt s) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = _ := by ring

/-- The paper's family-specific sharp support law under clipped interval
    uncertainty, for both fixed and minimum anchor shares. -/
theorem uniformMinimumIntervalTotalSupport_sharp (m : ℕ) (hm : (2 : ℕ) ≤ m) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (he : 0 < ε+δ) (he1 : ε+δ ≤ 1) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+δ)) ≤
      (uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε δ hε hδ fixed : ℝ) ∧
    (uniformMinimumIntervalTotalSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε δ hε hδ fixed : ℝ) ≤
      ((5 : ℕ)*Real.sqrt (((8 : ℕ) : ℝ)/(3 : ℕ)))*min ((m : ℝ)+(2 : ℕ)) (1/Real.sqrt (ε+δ)) := by
  norm_num only [Nat.cast_ofNat] at *
  refine ⟨uniformMinimumIntervalTotalSupport_lower m (by omega) ε δ hε hδ he fixed,?_⟩
  have heff : 0 < ε+(3/8)*δ := by nlinarith
  have heff1 : ε+(3/8)*δ ≤ 1 := by nlinarith
  obtain ⟨q,u,B,hw,hcount⟩ := uniform_core_uncertainty_upper m (by omega) ε δ hε hδ heff heff1
  have hi := core_witness_interval fixed hw
  have hmin := uniformMinimumIntervalTotalSupport_le m (by omega) ε δ hε hδ fixed
    (twoShares (3/4)) q (twoCore u) (rigidityCross (uniformTarget m (1/4))) B hi
  have hminR : (uniformMinimumIntervalTotalSupport m (by omega) ε δ hε hδ fixed : ℝ) ≤
      (supportSize q : ℝ)+2 := by exact_mod_cast hmin
  apply le_trans hminR
  exact le_trans hcount (uncertainty_rate_comparison ((m : ℝ)+2) (ε+(3/8)*δ) (ε+δ)
    (by positivity) heff he (by nlinarith))

end
end SparseCompletion
