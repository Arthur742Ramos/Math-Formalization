/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.SupportMinimum

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem residual_rate_from_inverse_square (m H : ℕ) (hH : 1 ≤ H)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : 2*(H+1) ≤ m → 3/(1216*((H+1 : ℕ) : ℝ)^2) ≤ ε) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤ H := by
  norm_num only [Nat.cast_ofNat] at *
  have hr : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hc0 : 0 ≤ Real.sqrt (3/1216) := Real.sqrt_nonneg _
  have hc2 : (Real.sqrt (3/1216))^2 = (3/1216 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : Real.sqrt (3/1216)/2 ≤ 1/3 := by nlinarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  by_cases hdim : 2*(H+1) ≤ m
  · have hh := hbound hdim
    have hN : (0 : ℝ) < (H+1 : ℕ) := by positivity
    have hs : (3/1216 : ℝ) ≤ ε*((H+1 : ℕ) : ℝ)^2 := by
      have h := (div_le_iff₀ (show 0 < 1216*((H+1 : ℕ) : ℝ)^2 by positivity)).mp hh
      nlinarith
    have heq : (Real.sqrt ε*((H+1 : ℕ) : ℝ))^2 = ε*((H+1 : ℕ) : ℝ)^2 := by
      rw [mul_pow,Real.sq_sqrt (le_of_lt hε)]
    have hroot : Real.sqrt (3/1216) ≤ Real.sqrt ε*((H+1 : ℕ) : ℝ) := by
      have hnn := mul_nonneg (le_of_lt hr) (le_of_lt hN)
      nlinarith
    have hdiv : Real.sqrt (3/1216)/(2*Real.sqrt ε) ≤ (H : ℝ) := by
      apply (div_le_iff₀ (show 0 < 2*Real.sqrt ε by positivity)).mpr
      norm_num only [Nat.cast_add,Nat.cast_one] at hroot
      nlinarith
    calc
      _ ≤ (Real.sqrt (3/1216)/2)*(1/Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = Real.sqrt (3/1216)/(2*Real.sqrt ε) := by ring
      _ ≤ _ := hdiv
  · have hdimR : (m : ℝ) ≤ 3*(H : ℝ) := by
      exact_mod_cast (show m ≤ 3*H by omega)
    calc
      _ ≤ (Real.sqrt (3/1216)/2)*(m : ℝ) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ ≤ (1/3)*(m : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ ≤ _ := by linarith

theorem uniform_witness_fixed_residual_positive {m : ℕ} {ε : ℝ}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε true a q B) : 1 ≤ supportSize q := by
  classical
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨_,_,ha,hnorm,_⟩
  have hmass : ∑ j, q j = 1/4 := by
    rw [ha trivial,Fin.sum_univ_two] at hnorm
    norm_num [twoShares] at hnorm
    linarith
  have hex : ∃ j, q j ≠ 0 := by
    by_contra hh
    push Not at hh
    simp only [hh,Finset.sum_const_zero] at hmass
    norm_num at hmass
  obtain ⟨j,hj⟩ := hex
  exact Finset.card_pos.mpr ⟨j,by simp [residualSupport,hj]⟩

theorem uniform_witness_small_residual_positive {m : ℕ} (hm : 2 ≤ m) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(1024 : ℕ)) {fixed : Bool}
    {a : Fin 2 → ℝ} {q : Fin m → ℝ} {B : Fin m → Fin m → ℝ}
    (hw : UniformWitness m ε fixed a q B) : 1 ≤ supportSize q := by
  norm_num only [Nat.cast_ofNat] at *
  by_contra hh
  have hzero : supportSize q=0 := by omega
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  have hd : 2*(supportSize q+1) ≤ m := by omega
  have hbound := uniform_minimum_share_inverse_square (by omega) q a hq ha hnorm hd B hB
    (fun i j => (hb i j).1) ε hε hresp
  norm_num [hzero] at hbound
  linarith

theorem uniform_witness_residual_lower {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) {fixed : Bool} {a : Fin 2 → ℝ} {q : Fin m → ℝ}
    {B : Fin m → Fin m → ℝ} (hw : UniformWitness m ε fixed a q B)
    (hpos : 1 ≤ supportSize q) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤ supportSize q := by
  norm_num only [Nat.cast_ofNat] at *
  apply residual_rate_from_inverse_square m (supportSize q) hpos ε hε
  intro hdim
  simp only [UniformWitness,Nat.cast_ofNat] at hw
  rcases hw with ⟨hq,ha,_,hnorm,hB,hb,hresp⟩
  exact uniform_minimum_share_inverse_square hm q a hq ha hnorm hdim B hB
    (fun i j => (hb i j).1) ε (le_of_lt hε) hresp

/-- The residual count of the attained total minimum. Both anchors have
    strictly positive mass, so subtracting two gives the residual minimum. -/
def uniformMinimumResidualSupport (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  uniformMinimumTotalSupport m hm ε hε fixed-2

theorem uniformMinimumResidualSupport_attained (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ (a : Fin 2 → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      UniformWitness m ε fixed a q B ∧ supportSize q=uniformMinimumResidualSupport m hm ε hε fixed := by
  obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumTotalSupport_attained m hm ε hε fixed
  exact ⟨a,q,B,hw,by rw [uniformMinimumResidualSupport,←hcount]; omega⟩

theorem uniformMinimumResidualSupport_le (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) (a : Fin 2 → ℝ) (q : Fin m → ℝ)
    (B : Fin m → Fin m → ℝ) (hw : UniformWitness m ε fixed a q B) :
    uniformMinimumResidualSupport m hm ε hε fixed ≤ supportSize q := by
  have hh := uniformMinimumTotalSupport_le m hm ε hε fixed a q B hw
  unfold uniformMinimumResidualSupport
  omega

theorem uniformMinimumResidualSupport_zero (m : ℕ) (hm : 2 ≤ m) (fixed : Bool) :
    uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) 0 (le_refl 0) fixed=m := by
  rw [uniformMinimumResidualSupport,uniformMinimumTotalSupport_zero m hm fixed]
  omega

theorem uniformMinimumResidualSupport_upper (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (fixed : Bool) :
    (uniformMinimumResidualSupport m hm ε (le_of_lt hε) fixed : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  obtain ⟨q,B,hq,hqm,hB,hb,hresp,hcount,_⟩ := uniform_sparse_upper_rate hm ε hε hε1
  have hw : UniformWitness m ε fixed (twoShares (3/4)) q B := by
    unfold UniformWitness
    norm_num only [Nat.cast_ofNat]
    refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,hresp⟩
    rw [hqm,Fin.sum_univ_two]
    norm_num [twoShares]
  have hmin := uniformMinimumResidualSupport_le m hm ε (le_of_lt hε) fixed (twoShares (3/4)) q B hw
  exact le_trans (by exact_mod_cast hmin) hcount

theorem uniformMinimumResidualSupport_fixed_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤
      (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) true : ℝ) ∧
    (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) true : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumResidualSupport_attained m (by omega) ε (le_of_lt hε) true
    have hh := uniform_witness_residual_lower (by omega) hε hw (uniform_witness_fixed_residual_positive hw)
    have heq : (supportSize q : ℝ) = (uniformMinimumResidualSupport m (by omega) ε (le_of_lt hε) true : ℝ) := by exact_mod_cast hcount
    rwa [heq] at hh
  · exact uniformMinimumResidualSupport_upper m (by omega) ε hε hε1 true

theorem uniformMinimumResidualSupport_natural_sharp (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ 1/(1024 : ℕ)) :
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ))*min (m : ℝ) (1/Real.sqrt ε) ≤
      (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) false : ℝ) ∧
    (uniformMinimumResidualSupport m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hm) ε (le_of_lt hε) false : ℝ) ≤
      3*min (m : ℝ) (1/Real.sqrt ε) := by
  norm_num only [Nat.cast_ofNat] at *
  constructor
  · obtain ⟨a,q,B,hw,hcount⟩ := uniformMinimumResidualSupport_attained m (by omega) ε (le_of_lt hε) false
    have hh := uniform_witness_residual_lower (by omega) hε hw
      (uniform_witness_small_residual_positive hm (le_of_lt hε) hsmall hw)
    have heq : (supportSize q : ℝ) = (uniformMinimumResidualSupport m (by omega) ε (le_of_lt hε) false : ℝ) := by exact_mod_cast hcount
    rwa [heq] at hh
  · exact uniformMinimumResidualSupport_upper m (by omega) ε hε (by linarith) false

end
end SparseCompletion
