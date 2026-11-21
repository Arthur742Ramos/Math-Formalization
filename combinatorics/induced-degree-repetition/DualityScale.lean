module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

@[expose] def rounds (n : ℕ) := Nat.log 2 (n+2)/4 + 1
@[expose] noncomputable def scale (n : ℕ) : ℝ := 1 + n/Real.log (n+2 : ℝ)

theorem rounds_pos (n : ℕ) : 0 < rounds n := Nat.succ_pos _
theorem scale_one (n : ℕ) : 1 ≤ scale n := by
  have hp : 0 < Real.log (n+2 : ℝ) := Real.log_pos (by linarith [(Nat.cast_nonneg n : 0 ≤ (n:ℝ))])
  unfold scale
  linarith [div_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) hp.le]

private theorem discrete_budget (n : ℕ) :
    (rounds n)^2 * 2^(rounds n+1) ≤ 32*(n+2) := by
  let L := rounds n
  let l := Nat.log 2 (n+2)
  have hL : L = l/4+1 := rfl
  have h : L ≤ 2^L := by
    have p (k : ℕ) : k ≤ 2^k := by
      induction k with
      | zero => decide
      | succ k ih => rw [pow_succ]; have := Nat.two_pow_pos k; omega
    exact p L
  have hlow := Nat.pow_log_le_self 2 (show n+2 ≠ 0 by omega)
  calc
    _ ≤ (2^L)^2 * 2^(L+1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h 2)
    _ = 2^(2*L+(L+1)) := by rw [← pow_mul,← pow_add]; congr 1; omega
    _ ≤ 2^(5+l) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 32*2^l := by rw [pow_add]; norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ hlow

theorem scales (n : ℕ) :
    (rounds n : ℝ)*2^(rounds n+1) ≤ 192*scale n ∧
    (n/rounds n+1 : ℕ) ≤ (5:ℝ)*scale n := by
  let L := rounds n
  have lp : 0 < (L:ℝ) := by exact_mod_cast rounds_pos n
  have l1 : 1 ≤ (L:ℝ) := by exact_mod_cast rounds_pos n
  have logp : 0 < Real.log (n+2 : ℝ) := Real.log_pos (by linarith [(Nat.cast_nonneg n : 0 ≤ (n:ℝ))])
  have nh : n+2 ≤ 2^(4*L) := (Nat.lt_pow_of_log_lt (by decide : 1<2)
    (show Nat.log 2 (n+2) < 4*L by dsimp [L,rounds]; omega)).le
  have upper := Real.log_le_log (by positivity : 0 < (n+2:ℝ))
    (show (n+2:ℝ) ≤ (2:ℝ)^(4*L) by exact_mod_cast nh)
  rw [Real.log_pow] at upper
  push_cast at upper
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hlog : Real.log (n+2 : ℝ) ≤ 4*L := upper.trans (by nlinarith [mul_le_mul_of_nonneg_left log2 (show 0 ≤ 4*(L:ℝ) by positivity)])
  have ratio : (n:ℝ)/L ≤ 4*(n/Real.log (n+2 : ℝ)) := by
    rw [← mul_div_assoc,div_le_div_iff₀ lp logp]
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)]
  have two : 2/(L:ℝ) ≤ 2 := (div_le_iff₀ lp).mpr (by linarith)
  have disc : (L:ℝ)^2 * 2^(L+1) ≤ 32*(n+2 : ℝ) := by exact_mod_cast discrete_budget n
  have small : (L:ℝ)*2^(L+1) ≤ 32*((n:ℝ)/L+2/L) := by
    rw [← add_div,← mul_div_assoc,le_div_iff₀ lp]
    nlinarith
  constructor
  · change (L:ℝ)*2^(L+1) ≤ 192*(1+(n:ℝ)/Real.log (n+2 : ℝ))
    linarith [div_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) logp.le]
  · have dn : ((n/L:ℕ):ℝ) ≤ (n:ℝ)/L := (le_div_iff₀ lp).mpr (by exact_mod_cast Nat.div_mul_le_self n L)
    push_cast
    change ((n/L:ℕ):ℝ)+1 ≤ 5*(1+(n:ℝ)/Real.log (n+2 : ℝ))
    linarith [div_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) logp.le]

end InducedDegreeRepetition.Duality
