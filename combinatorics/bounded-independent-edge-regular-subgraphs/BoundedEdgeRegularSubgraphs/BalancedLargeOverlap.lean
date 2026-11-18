module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Fresh-edge damping of the large overlaps in balanced arrays
-/

public section

namespace BoundedEdgeRegularSubgraphs

/-- The logarithmic inequality for the number of unshared vertices
used in Theorem 4.1. -/
theorem balanced_overlap_log_le {k j r : ℝ} (hk : 4 ≤ k) (hr : 0 ≤ r)
    (hre : r = k - j) (hj : (3 / 4 : ℝ) * k ≤ j) :
    r * Real.log k - j * Real.log (r + 1) ≤ k * Real.log 4 := by
  have hk₀ : 0 < k := by linarith
  let t := 4 * r / k
  have ht₀ : 0 ≤ t := by dsimp only [t]; positivity
  have ht₁ : t ≤ 1 := by
    dsimp only [t]
    exact (div_le_iff₀ hk₀).2 (by linarith only [hre, hj])
  have hc : (1 - t) • Real.log 1 + t • Real.log (1 + k / 4) ≤
      Real.log ((1 - t) • (1 : ℝ) + t • (1 + k / 4)) :=
    strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (1 + k / 4 : ℝ) ∈ Set.Ioi 0 by
      apply Set.mem_Ioi.mpr
      positivity)
    (sub_nonneg.mpr ht₁) ht₀ (by ring)
  have hrec : (1 - t) * 1 + t * (1 + k / 4) = r + 1 := by
    dsimp only [t]
    field_simp [hk₀.ne'] <;> ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, hrec] at hc
  have hbase : Real.log k - Real.log 4 ≤ Real.log (1 + k / 4) := by
    rw [← Real.log_div hk₀.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlog : 0 ≤ Real.log k - Real.log 4 :=
    sub_nonneg.mpr (Real.log_le_log (by norm_num) hk)
  have hprod : r ≤ j * t := by
    have h := mul_le_mul_of_nonneg_right (show k / 4 ≤ j by linarith only [hj, hk]) ht₀
    have he : k / 4 * t = r := by dsimp only [t]; field_simp [hk₀.ne'] <;> ring
    rwa [he] at h
  have ht : r * (Real.log k - Real.log 4) ≤ j * Real.log (r + 1) := by
    have hj₀ : 0 ≤ j := by linarith only [hj, hk]
    calc
      _ ≤ (j * t) * (Real.log k - Real.log 4) :=
        mul_le_mul_of_nonneg_right hprod hlog
      _ = j * (t * (Real.log k - Real.log 4)) := by ring
      _ ≤ j * Real.log (r + 1) :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hbase ht₀).trans hc) hj₀
  have hR : r ≤ k := by linarith only [hre, hj, hk]
  nlinarith only [ht, mul_le_mul_of_nonneg_right hR (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))]

/-- Choosing the size constant of the ambient block absorbs the entire
large-overlap term, even when the two candidates coincide. -/
theorem balanced_overlap_fresh_product_le_exp {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {k j N : ℕ}, 4 ≤ k → j ≤ k → (3 / 4 : ℝ) * (k : ℝ) ≤ j →
      L * (k : ℝ) * Real.sqrt k ≤ (N : ℝ) →
      Real.exp ((k : ℝ) * Real.log k / 2 + A * k) *
        ((Real.exp 1 * (k : ℝ) / ((3 / 4 : ℝ) * N)) ^ j) *
        ((C / Real.sqrt ((k - j : ℕ) + 1)) ^ j) ≤ Real.exp (-(k : ℝ)) := by
  let b := 1 - Real.log (3 / 4 : ℝ) + Real.log C
  let D := A + |b| + Real.log 4 / 2 + 1
  let L := Real.exp (D / (3 / 4))
  have hD : 0 < D := by
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    linarith only [hA, abs_nonneg b, hl]
  have hL : 1 ≤ L := Real.one_le_exp (by positivity)
  refine ⟨L, hL, ?_⟩
  intro k j N hk hj hlarge hN
  let r := ((k - j : ℕ) : ℝ)
  let g := Real.exp 1 * (k : ℝ) / ((3 / 4 : ℝ) * N)
  let f := C / Real.sqrt (r + 1)
  have hk₄ : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) < k := by linarith
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hN₀ : (0 : ℝ) < N := (show 0 < L * (k : ℝ) * Real.sqrt k by
    exact mul_pos (mul_pos (Real.exp_pos _) hk₀) (Real.sqrt_pos.mpr hk₀)).trans_le hN
  have hL₀ : 0 < L := Real.exp_pos _
  have hg : 0 < g := by dsimp only [g]; positivity
  have hf : 0 < f := by dsimp only [f]; positivity
  have hrDef : r = (k : ℝ) - j := Nat.cast_sub hj
  have h1 := Real.log_le_log (show 0 < L * (k : ℝ) * Real.sqrt k by positivity) hN
  rw [Real.log_mul (by positivity) (Real.sqrt_pos.mpr hk₀).ne',
    Real.log_mul hL₀.ne' hk₀.ne', Real.log_sqrt hk₀.le] at h1
  have h2 : Real.log g + Real.log f ≤ b - Real.log L - Real.log k / 2 - Real.log (r + 1) / 2 := by
    dsimp only [g, f, b]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (Real.exp_pos _).ne' hk₀.ne',
      Real.log_exp, Real.log_mul (by norm_num : (3 / 4 : ℝ) ≠ 0) hN₀.ne',
      Real.log_div hC.ne' (Real.sqrt_pos.mpr (by positivity)).ne', Real.log_sqrt (by positivity)]
    linarith only [h1]
  have h3 := balanced_overlap_log_le hk₄ hr hrDef hlarge
  have hLogL : Real.log L = D / (3 / 4) := Real.log_exp _
  have hDk : (k : ℝ) * D ≤ (j : ℝ) * Real.log L := by
    rw [hLogL]
    have ha := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ D / (3 / 4) by positivity)
    nlinarith only [ha]
  have hb' : (j : ℝ) * b ≤ (k : ℝ) * |b| :=
    (mul_le_mul_of_nonneg_left (le_abs_self b) (Nat.cast_nonneg j)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (abs_nonneg b))
  have hExp : (k : ℝ) * Real.log k / 2 + A * k +
      (j : ℝ) * Real.log g + (j : ℝ) * Real.log f ≤ -(k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    dsimp only [D] at hDk
    nlinarith only [h, hDk, hb', h3, congrArg (fun x : ℝ ↦ x * Real.log k) hrDef]
  change Real.exp ((k : ℝ) * Real.log k / 2 + A * k) * g ^ j * f ^ j ≤ _
  calc
    _ = Real.exp ((k : ℝ) * Real.log k / 2 + A * k +
      (j : ℝ) * Real.log g + (j : ℝ) * Real.log f) := by
        simp only [Real.exp_add, Real.exp_nat_mul, Real.exp_log hg, Real.exp_log hf]
    _ ≤ _ := Real.exp_le_exp.mpr hExp

end BoundedEdgeRegularSubgraphs
