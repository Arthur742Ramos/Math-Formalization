module

public import DualityScale
public import DualityBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

@[expose] noncomputable def floorBias (n : ℕ) := (1/8 : ℝ)^(2^(rounds n+1))
@[expose] noncomputable def growth (q n : ℕ) := (q:ℝ)^(n/rounds n+1)
@[expose] noncomputable def lossConstant (q C : ℕ) : ℝ :=
  192*((4+3*(C:ℝ))*Real.log 8 + (3+3*(C:ℝ))*Real.log q)

theorem loss_le_fraction (q C n : ℕ) (hq : 2 ≤ q) :
    Real.exp (-(lossConstant q C)*scale n) ≤ fraction q C (rounds n) (floorBias n) (growth q n) := by
  let L := rounds n
  let m := 2^(L+1)
  let k := n/L+1
  let M := 192*scale n
  have l1 : 1 ≤ (L:ℝ) := by exact_mod_cast rounds_pos n
  have m1 : 1 ≤ (m:ℝ) := by dsimp [m]; exact_mod_cast (Nat.two_pow_pos (L+1))
  have sc := scales n
  have lm : (L:ℝ)*m ≤ M := by exact_mod_cast sc.1
  have hs := scale_one n
  have hm : (m:ℝ) ≤ M := (le_mul_of_one_le_left (by positivity) l1).trans lm
  have hl : (L:ℝ) ≤ M := (le_mul_of_one_le_right (by positivity) m1).trans lm
  have hk : (k:ℝ) ≤ M := by dsimp [M]; linarith [sc.2]
  have h1 : 1 ≤ M := m1.trans hm
  have q0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have lq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have l8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have rb : 0 < floorBias n := by unfold floorBias; positivity
  have kg : 0 < growth q n := by unfold growth; positivity
  have frac : 0 < fraction q C L (floorBias n) (growth q n) := by unfold fraction; positivity
  apply (Real.le_log_iff_exp_le frac).mp
  have rbLog : Real.log (floorBias n) = -(m:ℝ)*Real.log 8 := by
    simp [floorBias,Real.log_pow,m,L]
  have kLog : Real.log (growth q n) = (k:ℝ)*Real.log q := by rw [growth,Real.log_pow]
  have logFrac : Real.log (fraction q C L (floorBias n) (growth q n)) =
      -(((L:ℝ)*m+(3+3*(C:ℝ))*m)*Real.log 8 +
        ((L:ℝ)+2+3*(C:ℝ)*k)*Real.log q) := by
    unfold fraction
    rw [Real.log_mul (by positivity) (by positivity)]
    simp (disch := positivity) only [Real.log_pow,Real.log_div,rbLog,kLog,Nat.cast_add,
      Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [logFrac]
  have c0 : 0 ≤ 3*(C:ℝ) := by positivity
  have h8 : (L:ℝ)*m+(3+3*(C:ℝ))*m ≤ (4+3*(C:ℝ))*M := by
    nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 3+3*(C:ℝ) by positivity)]
  have hq' : (L:ℝ)+2+3*(C:ℝ)*k ≤ (3+3*(C:ℝ))*M := by
    linarith [mul_le_mul_of_nonneg_left hk c0]
  have bound := add_le_add (mul_le_mul_of_nonneg_right h8 l8) (mul_le_mul_of_nonneg_right hq' lq)
  dsimp [M] at bound
  unfold lossConstant
  linarith

end InducedDegreeRepetition.Duality
