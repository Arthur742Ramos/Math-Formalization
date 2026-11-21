module

public import AmplificationRates
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Filter
open scoped Topology

@[expose] noncomputable def residueRate (a κ : ℝ) (L : ℕ) :=
  levelRate a κ (Nat.log 2 L)/2

theorem dyadic_rate (a κ : ℝ) (j : ℕ) :
    residueRate a κ (2^j) = levelRate a κ j / 2 := by simp [residueRate,Nat.log_pow]

theorem rate_limit (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    Tendsto (fun j : ℕ => residueRate a κ (2^j)/Real.log ((2:ℝ)^j+1)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro t
  have slope : 0 < a*κ^2/256 := by positivity
  obtain ⟨j₀,h₀⟩ := exists_nat_gt (t/(a*κ^2/256))
  filter_upwards [eventually_ge_atTop j₀,eventually_ge_atTop 8] with j hj hj8
  have tj := (div_lt_iff₀ slope).mp (h₀.trans_le (show (j₀:ℝ) ≤ j by exact_mod_cast hj))
  have jpos : (0:ℝ) < j := by exact_mod_cast (by omega : 0<j)
  have logp : 0 < Real.log ((2:ℝ)^j+1) := Real.log_pos (by linarith [pow_pos (by norm_num : (0:ℝ)<2) j])
  have cap : Real.log ((2:ℝ)^j+1) ≤ 2*j := by
    have p := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)
    have le := Real.log_le_log (by positivity) (show (2:ℝ)^j+1 ≤ 2^(j+1) by rw [pow_succ]; linarith)
    rw [Real.log_pow] at le
    push_cast at le
    have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    nlinarith [mul_le_mul_of_nonneg_left log2 (show 0 ≤ (j:ℝ)+1 by positivity),
      (show (1:ℝ)≤j by exact_mod_cast (by omega : 1≤j))]
  have floor : (j:ℝ)/8 ≤ (j/4:ℕ) := by
    have h : j ≤ 8*(j/4) := by omega
    have e : (j:ℝ) ≤ 8*((j/4:ℕ):ℝ) := by exact_mod_cast h
    linarith
  have bern (n : ℕ) : 1+(n:ℝ)*κ ≤ (1+κ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,Nat.cast_succ]
      have h := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+κ by linarith)
      nlinarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) (sq_nonneg κ)]
  have b : (j:ℝ)/8*κ ≤ (1+κ)^(j/4) := by linarith [mul_le_mul_of_nonneg_right floor hk.le,bern (j/4)]
  have sq := (sq_le_sq₀ (by positivity) (by positivity)).mpr b
  rw [← pow_mul] at sq
  have up := pow_le_pow_right₀ (show (1:ℝ)≤1+κ by linarith) (show j/4*2 ≤ j/2 by omega)
  have big := mul_le_mul_of_nonneg_left (sq.trans up) ha.le
  rw [dyadic_rate,le_div_iff₀ logp]
  unfold levelRate
  by_cases neg : t < 0
  · exact (mul_nonpos_of_nonpos_of_nonneg neg.le logp.le).trans (by positivity)
  have cc := mul_le_mul_of_nonneg_left cap (le_of_not_gt neg)
  have h := mul_le_mul_of_nonneg_right tj.le (show 0 ≤ (2:ℝ)*j by positivity)
  nlinarith only [cc,h,big]

end InducedDegreeRepetition.Duality
