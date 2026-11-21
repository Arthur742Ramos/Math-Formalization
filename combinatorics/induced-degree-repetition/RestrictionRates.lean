module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Filter
open scoped Topology

@[expose] noncomputable def generatorRate (q : ℕ) (D : ℝ) := (D+Real.log q)/Real.log 2
@[expose] noncomputable def sampleRate (q : ℕ) (D u γ : ℝ) := 1+4*generatorRate q D+u/γ

theorem rate_positive (q : ℕ) (hq : 3 ≤ q) (D u γ : ℝ) (hd : 0<D) (hu : 0<u) (hg : 0<γ) :
    0 < generatorRate q D ∧ 1 ≤ sampleRate q D u γ := by
  have lq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1<q))
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have p : 0 < generatorRate q D := by dsimp [generatorRate]; positivity
  refine ⟨p,?_⟩
  dsimp [sampleRate]
  linarith [div_pos hu hg]

theorem generator_budget (q : ℕ) (hq : 3 ≤ q) (D : ℝ) (r s : ℕ) (hr : 1 ≤ r)
    (h : (2:ℝ)^s ≤ q*Real.exp (D*r)) : (s:ℝ) ≤ generatorRate q D*r := by
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have lq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1≤q))
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have b := Real.log_le_log (by positivity) h
  rw [Real.log_pow,Real.log_mul qp.ne' (Real.exp_pos _).ne',Real.log_exp] at b
  dsimp [generatorRate]
  rw [div_mul_eq_mul_div,le_div_iff₀ l2]
  have r1 : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  nlinarith [le_mul_of_one_le_left lq r1]

/-- Bounds on the undesignated positions. -/
theorem free_budget (q : ℕ) (hq : 3 ≤ q) (D u γ : ℝ) (hd : 0<D) (hu : 0<u) (hg : 0<γ)
    (r s : ℕ) (small : (s:ℝ) ≤ generatorRate q D*r) :
    let n := ⌈sampleRate q D u γ*r⌉₊
    (n:ℝ)/2 ≤ (n-s:ℕ) ∧ u*r/8 ≤ γ*(n-s:ℕ) := by
  let C := sampleRate q D u γ
  let n := ⌈C*r⌉₊
  have ceil : C*r ≤ n := Nat.le_ceil _
  have rr : (0:ℝ)≤r := Nat.cast_nonneg _
  have gpos := (rate_positive q hq D u γ hd hu hg).1
  have b : 2*(generatorRate q D) ≤ C := by dsimp [C,sampleRate]; linarith [div_pos hu hg]
  have s2 : 2*(s:ℝ) ≤ n := by nlinarith [mul_le_mul_of_nonneg_right b rr]
  have sn : s ≤ n := by exact_mod_cast (show (s:ℝ) ≤ n by linarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)])
  change (n:ℝ)/2 ≤ ((n-s:ℕ):ℝ) ∧ u*r/8 ≤ γ*((n-s:ℕ):ℝ)
  rw [Nat.cast_sub sn]
  constructor
  · linarith
  · have uc : u ≤ γ*C := by dsimp [C,sampleRate]; field_simp; nlinarith [mul_pos hg gpos]
    nlinarith [mul_le_mul_of_nonneg_right uc rr,mul_le_mul_of_nonneg_left ceil hg.le,
      mul_le_mul_of_nonneg_left s2 hg.le,mul_nonneg hu.le rr]

/-- Convert the complete-sample moment estimate into the exponential tail used by
the restriction lemma. The eventual cutoff depends on u, the exponent does not
depend on the subgroup budget. -/
theorem moment_rate (u : ℝ) (hu : 0<u) : ∀ᶠ r : ℕ in atTop,
    ∀ (n k m : ℕ) (γ : ℝ), 0 < γ → γ ≤ 1/2 → (n:ℝ)/2 ≤ k → (n:ℝ)/2 ≤ m →
    u*r/8 ≤ γ*m →
    (Real.exp (-u*r/8) + (1-γ)^m)^k + Real.exp (-u*r/8)^m ≤ 2*Real.exp (-u*r*n/32) := by
  obtain ⟨r₀,hr₀⟩ := exists_nat_gt (16*Real.log 2/u)
  filter_upwards [eventually_ge_atTop r₀] with r rr
  intro n k m γ hg hg' hk hm scale
  have r0 : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have enough := (div_lt_iff₀ hu).mp (hr₀.trans_le (show (r₀:ℝ) ≤ r by exact_mod_cast rr))
  have b : 1-γ ≤ Real.exp (-γ) := by linarith [Real.add_one_le_exp (-γ)]
  have shrink := pow_le_pow_left₀ (by linarith) b m
  rw [← Real.exp_nat_mul] at shrink
  have e := shrink.trans (Real.exp_le_exp.mpr (by nlinarith : (m:ℝ)*(-γ) ≤ -u*r/8))
  have sum : Real.exp (-u*r/8)+(1-γ)^m ≤ Real.exp (-u*r/16) := by
    apply (add_le_add_right e _).trans
    rw [← two_mul,← Real.exp_log (by norm_num : (0:ℝ)<2),← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have power := pow_le_pow_left₀ (add_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) m)) sum k
  rw [← Real.exp_nat_mul] at power
  have h1 : (Real.exp (-u*r/8)+(1-γ)^m)^k ≤ Real.exp (-u*r*n/32) := power.trans
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg hu.le r0)]))
  have h2 : Real.exp (-u*r/8)^m ≤ Real.exp (-u*r*n/32) := by
    rw [← Real.exp_nat_mul,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hm (mul_nonneg hu.le r0),mul_nonneg (mul_nonneg hu.le r0) (Nat.cast_nonneg n : (0:ℝ)≤n)]
  linarith

theorem union_rate (u : ℝ) (hu : 0<u) : ∀ᶠ r : ℕ in atTop, ∀ n : ℕ, 1 ≤ n →
    (2:ℝ)^n*2^n*(2*Real.exp (-u*r*n/32)) ≤ Real.exp (-u*r*n/64) := by
  obtain ⟨r₀,hr₀⟩ := exists_nat_gt (192*Real.log 2/u)
  filter_upwards [eventually_ge_atTop r₀] with r rr
  intro n hn
  have enough := (div_lt_iff₀ hu).mp (hr₀.trans_le (show (r₀:ℝ) ≤ r by exact_mod_cast rr))
  have n1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have l2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ = Real.exp ((n:ℝ)*Real.log 2+(n:ℝ)*Real.log 2+(Real.log 2-u*r*n/32)) := by
      simp only [Real.exp_add,sub_eq_add_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      congr 2; ring_nf
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left enough.le (Nat.cast_nonneg n : (0:ℝ)≤n),le_mul_of_one_le_left l2 n1])

end InducedDegreeRepetition.Restriction
