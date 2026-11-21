module

public import HostScales
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Filter Finset
open scoped Classical Topology

@[expose] def blockLength (k L₀ L₁ : ℕ) (i : Fin (k+k)) := if i.val<k then L₀ else L₁

theorem block_counts (k L₀ L₁ : ℕ) (ne : L₀ ≠ L₁) :
    (univ.filter fun i => blockLength k L₀ L₁ i=L₀).card=k ∧
    (univ.filter fun i => blockLength k L₀ L₁ i=L₁).card=k ∧
    (∑ i, blockLength k L₀ L₁ i) = k*(L₀+L₁) := by
  classical
  have left (i : Fin k) : blockLength k L₀ L₁ (Fin.castAdd k i)=L₀ := by simp [blockLength]
  have right (i : Fin k) : blockLength k L₀ L₁ (i.addNat k)=L₁ := by simp [blockLength]
  constructor
  · calc
      _ = ∑ i, if blockLength k L₀ L₁ i=L₀ then (1:ℕ) else 0 := by simp
      _ = _ := by rw [Fin.sum_univ_add]; simp [left,right,ne.symm]
  constructor
  · calc
      _ = ∑ i, if blockLength k L₀ L₁ i=L₁ then (1:ℕ) else 0 := by simp
      _ = _ := by rw [Fin.sum_univ_add]; simp [left,right,ne]
  · rw [Fin.sum_univ_add]; simp [left,right,Nat.mul_add]

/-- Real bounds on the integer tester and reference block sizes. -/
theorem eventual_block_sizes (g L n₁ : ℕ) (α a : ℝ) (gp : 0 < g) (Lp : 0 < L)
    (ap : 0 < α) (a1 : α ≤ 1) (room : 8 ≤ a*g) :
    ∀ᶠ r : ℕ in atTop,
      let s := ⌈4*(r:ℝ)/g⌉₊
      let k := ⌈α*r/L⌉₊
      let m := k*L
      0 < r ∧ 0 < k ∧ n₁ ≤ k ∧ k+k ≤ r^2 ∧ 4*r ≤ g*s ∧ g*s ≤ 5*r ∧
      (g-1)*s ≤ 4*r ∧ (s:ℝ) ≤ a*r ∧ α*r ≤ m ∧ (m:ℝ) ≤ 2*α*r := by
  have gpos : (0:ℝ)<g := by exact_mod_cast gp
  have Lpos : (0:ℝ)<L := by exact_mod_cast Lp
  obtain ⟨R,hR⟩ := exists_nat_gt (max ((n₁+1:ℝ)*L/α) ((g:ℝ)^2+g+4))
  filter_upwards [eventually_ge_atTop R] with r hr
  have big := hR.trans_le (show (R:ℝ) ≤ r by exact_mod_cast hr)
  have h := (div_lt_iff₀ ap).mp ((le_max_left ..).trans_lt big)
  have G := (le_max_right ..).trans_lt big
  let k := ⌈α*(r:ℝ)/L⌉₊
  let s := ⌈4*(r:ℝ)/g⌉₊
  have kp : α*r ≤ (k:ℝ)*L := (div_le_iff₀ Lpos).mp (Nat.le_ceil _)
  have klt : (k:ℝ)*L < α*r+L := by
    have z := (Nat.ceil_lt_add_one (show 0 ≤ α*(r:ℝ)/L by positivity))
    have m := mul_lt_mul_of_pos_right z Lpos
    dsimp [k]
    rwa [add_mul,div_mul_cancel₀ _ Lpos.ne',one_mul] at m
  have sp : 4*(r:ℝ) ≤ (s:ℝ)*g := (div_le_iff₀ gpos).mp (Nat.le_ceil _)
  have slt : (s:ℝ)*g < 4*r+g := by
    have z := Nat.ceil_lt_add_one (show 0 ≤ 4*(r:ℝ)/g by positivity)
    have m := mul_lt_mul_of_pos_right z gpos
    dsimp [s]
    rwa [add_mul,div_mul_cancel₀ _ gpos.ne',one_mul] at m
  have L1 : 1 ≤ (L:ℝ) := by exact_mod_cast Lp
  have g1 : 1 ≤ (g:ℝ) := by exact_mod_cast gp
  have more : L ≤ α*(r:ℝ) := by nlinarith [mul_nonneg (Nat.cast_nonneg n₁ : (0:ℝ)≤n₁) Lpos.le]
  have nle : (n₁:ℝ) < k := lt_of_mul_lt_mul_right (a:=(L:ℝ)) (by nlinarith) Lpos.le
  have hrg : (g:ℝ) ≤ r := by nlinarith [sq_nonneg (g:ℝ)]
  have rg : 4 ≤ (r:ℝ) := by nlinarith [sq_nonneg (g:ℝ)]
  have ksmall : (k:ℝ) ≤ 2*r := by
    have one := le_mul_of_one_le_right (Nat.cast_nonneg k : (0:ℝ)≤k) L1
    have ar := mul_le_of_le_one_left (Nat.cast_nonneg r : (0:ℝ)≤r) a1
    linarith
  have bigs : (g:ℝ) ≤ s := by
    apply le_of_mul_le_mul_right (a:=(g:ℝ)) _ gpos
    nlinarith
  dsimp only
  refine ⟨by exact_mod_cast (by linarith : (0:ℝ)<r),by exact_mod_cast (Nat.cast_nonneg n₁|>.trans_lt nle),
    by exact_mod_cast nle.le,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast (by nlinarith [mul_le_mul_of_nonneg_right rg (Nat.cast_nonneg r : (0:ℝ)≤r)] : (k:ℝ)+k ≤ (r:ℝ)^2)
  · change 4*r ≤ g*s
    exact_mod_cast (by linarith : 4*(r:ℝ) ≤ g*s)
  · change g*s ≤ 5*r
    exact_mod_cast (by linarith : (g:ℝ)*s ≤ 5*r)
  · change (g-1)*s ≤ 4*r
    have := (show ((g-1:ℕ):ℝ)=(g:ℝ)-1 by rw [Nat.cast_sub gp]; norm_num)
    exact_mod_cast (by rw [this]; nlinarith : ((g-1:ℕ):ℝ)*s ≤ 4*r)
  · apply le_of_mul_le_mul_right (a:=(g:ℝ)) _ gpos
    nlinarith [mul_le_mul_of_nonneg_right room (Nat.cast_nonneg r : (0:ℝ)≤r)]
  · exact_mod_cast kp
  · exact_mod_cast (by linarith : (k:ℝ)*L ≤ 2*α*r)

end InducedDegreeRepetition.Sampling
