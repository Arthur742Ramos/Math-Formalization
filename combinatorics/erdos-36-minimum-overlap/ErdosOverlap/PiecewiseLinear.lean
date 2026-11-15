/-
Copyright (c) 2026. Released under the BSD-3-Clause license.

Exact nonnegative piecewise affine witnesses on a uniform rational grid.
Sparse data are represented by nonnegative integer nodal numerators and a
common positive denominator. Every omitted node has value zero.
-/
module

public import ErdosOverlap.ContinuousDual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set

namespace ErdosOverlap

public section

noncomputable section

/-- The compactly supported unit tent. -/
@[expose] def unitTent (x : ℝ) : ℝ := max (1 - |x|) 0

/-- A nodal tent on a grid with `n` cells. -/
@[expose] def gridTent (n i : ℕ) (t : ℝ) : ℝ :=
  unitTent ((n : ℝ) * t - i)

theorem unitTent_nonneg (x : ℝ) : 0 ≤ unitTent x := le_max_right _ _

theorem unitTent_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    unitTent x = 0 := by
  exact max_eq_right (by linarith)

theorem lipschitz_affine_real (a b : ℝ) :
    LipschitzWith ‖a‖₊ (fun x : ℝ => a * x + b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  rw [show a * x + b - (a * y + b) = a * (x - y) by ring, abs_mul]

theorem unitTent_lipschitz : LipschitzWith 1 unitTent := by
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have hsub := (LipschitzWith.const (1 : ℝ)).sub habs
  unfold unitTent
  convert! hsub.max_const 0 using 1
  simp

theorem gridTent_lipschitz (n i : ℕ) :
    LipschitzWith ‖(n : ℝ)‖₊ (gridTent n i) := by
  unfold gridTent
  convert! unitTent_lipschitz.comp (lipschitz_affine_real (n : ℝ) (-(i : ℝ))) using 1
  simp

theorem gridTent_nonneg (n i : ℕ) (t : ℝ) : 0 ≤ gridTent n i t :=
  unitTent_nonneg _

theorem integral_id_real (a b : ℝ) :
    (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
  have hp : ∀ t ∈ uIcc a b, HasDerivAt (fun x : ℝ => x * x / 2) t t := by
    intro t _
    convert ((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2 using 1 <;>
      simp [id_eq]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hp
    (continuous_id.intervalIntegrable a b)
  convert hi using 1
  ring

theorem unitTent_integral {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) :
    (∫ x in a..b, unitTent x) = 1 := by
  have hc := unitTent_lipschitz.continuous
  have hl : (∫ x in a..(-1 : ℝ), unitTent x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha] at hx
    apply unitTent_eq_zero_of_one_le_abs
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.2]
  have hr : (∫ x in (1 : ℝ)..b, unitTent x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hb] at hx
    apply unitTent_eq_zero_of_one_le_abs
    rw [abs_of_nonneg (by linarith [hx.1])]
    exact hx.1
  have hleft : (∫ x in (-1 : ℝ)..0, unitTent x) = 1 / 2 := by
    calc
      _ = ∫ x in (-1 : ℝ)..0, 1 + x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        rw [unitTent, abs_of_nonpos hx.2, max_eq_left (by linarith [hx.1])]
        ring
      _ = 1 / 2 := by
        have hi : IntervalIntegrable (fun x : ℝ => x) volume (-1) 0 :=
          continuous_id.intervalIntegrable (-1) 0
        have hsum := intervalIntegral.integral_add
          (intervalIntegrable_const (c := (1 : ℝ)) (μ := volume) (a := -1) (b := 0)) hi
        calc
          _ = (∫ _x in (-1 : ℝ)..0, (1 : ℝ)) + (∫ x in (-1 : ℝ)..0, x) := by
            convert! hsum using 1
          _ = _ := by rw [integral_id_real]; norm_num
  have hright : (∫ x in (0 : ℝ)..1, unitTent x) = 1 / 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, 1 - x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le zero_le_one] at hx
        rw [unitTent, abs_of_nonneg hx.1, max_eq_left (by linarith [hx.2])]
      _ = 1 / 2 := by
        have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
          continuous_id.intervalIntegrable 0 1
        have hsum := intervalIntegral.integral_sub
          (intervalIntegrable_const (c := (1 : ℝ)) (μ := volume) (a := 0) (b := 1)) hi
        calc
          _ = (∫ _x in (0 : ℝ)..1, (1 : ℝ)) - (∫ x in (0 : ℝ)..1, x) := by
            convert! hsum using 1
          _ = _ := by rw [integral_id_real]; norm_num
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a (-1)) (hc.intervalIntegrable (-1) 0)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a 0) (hc.intervalIntegrable 0 1)
  have h₃ := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a 1) (hc.intervalIntegrable 1 b)
  linarith

theorem gridTent_integral {n i : ℕ} (hn : 0 < n) (hi : 0 < i) (hin : i < n) :
    (∫ t in (0 : ℝ)..1, gridTent n i t) = 1 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hin1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
  unfold gridTent
  rw [intervalIntegral.integral_comp_mul_left (fun x => unitTent (x - i)) hn0]
  rw [intervalIntegral.integral_comp_sub_right]
  simp only [mul_zero, mul_one, zero_sub, smul_eq_mul]
  rw [unitTent_integral (by linarith) (by linarith)]
  simp

theorem gridTent_one {n i : ℕ} (hin : i < n) : gridTent n i 1 = 0 := by
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
  apply unitTent_eq_zero_of_one_le_abs
  simp only [mul_one]
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem gridTent_zero {n i : ℕ} (hi : 0 < i) : gridTent n i 0 = 0 := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  apply unitTent_eq_zero_of_one_le_abs
  simp only [mul_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  exact hi1

/-- One nonzero nodal numerator; all missing nodes are zero. -/
structure PLNode where
  index : ℕ
  numerator : ℕ
  deriving DecidableEq, Repr

/-- All stored nodes are strictly interior to the grid. -/
@[expose] def PLValid (n : ℕ) (nodes : List PLNode) : Prop :=
  ∀ p ∈ nodes, 0 < p.index ∧ p.index < n

instance (n : ℕ) (nodes : List PLNode) : Decidable (PLValid n nodes) :=
  inferInstanceAs (Decidable (∀ p ∈ nodes, 0 < p.index ∧ p.index < n))

/-- Exact total of the integer nodal numerators. -/
@[expose] def plMass (nodes : List PLNode) : ℕ := (nodes.map PLNode.numerator).sum

/-- The continuous piecewise affine interpolant represented by sparse nodal data. -/
@[expose] def plWitness (n den : ℕ) (nodes : List PLNode) (t : ℝ) : ℝ :=
  (nodes.map (fun p => ((p.numerator : ℝ) / den) * gridTent n p.index t)).sum

theorem plWitness_lipschitz (n den : ℕ) (nodes : List PLNode) :
    ∃ K : NNReal, LipschitzWith K (plWitness n den nodes) := by
  induction nodes with
  | nil =>
      refine ⟨0, ?_⟩
      unfold plWitness
      convert! (LipschitzWith.const (0 : ℝ)) using 1
  | cons p ps ih =>
      obtain ⟨K, hK⟩ := ih
      have hp := (lipschitz_affine_real ((p.numerator : ℝ) / den) 0).comp
        (gridTent_lipschitz n p.index)
      refine ⟨‖(p.numerator : ℝ) / den‖₊ * ‖(n : ℝ)‖₊ + K, ?_⟩
      convert! hp.add hK using 1
      funext t
      simp [plWitness]

theorem plWitness_continuous (n den : ℕ) (nodes : List PLNode) :
    Continuous (plWitness n den nodes) := by
  obtain ⟨_, hK⟩ := plWitness_lipschitz n den nodes
  exact hK.continuous

theorem plWitness_absolutelyContinuous (n den : ℕ) (nodes : List PLNode) :
    AbsolutelyContinuousOnInterval (plWitness n den nodes) 0 1 := by
  obtain ⟨_, hK⟩ := plWitness_lipschitz n den nodes
  exact hK.lipschitzOnWith.absolutelyContinuousOnInterval

theorem plWitness_nonneg (n den : ℕ) (nodes : List PLNode) (t : ℝ) :
    0 ≤ plWitness n den nodes t := by
  induction nodes with
  | nil => simp [plWitness]
  | cons p ps ih =>
      simp only [plWitness, List.map_cons, List.sum_cons] at ih ⊢
      exact add_nonneg (mul_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (gridTent_nonneg _ _ _)) ih

theorem plWitness_one {n den : ℕ} {nodes : List PLNode} (hvalid : PLValid n nodes) :
    plWitness n den nodes 1 = 0 := by
  induction nodes with
  | nil => simp [plWitness]
  | cons p ps ih =>
      have hp := hvalid p (List.mem_cons_self)
      have hps : PLValid n ps := fun q hq => hvalid q (List.mem_cons_of_mem _ hq)
      simp only [plWitness, List.map_cons, List.sum_cons, gridTent_one hp.2, mul_zero,
        zero_add] at ⊢
      exact ih hps

theorem plWitness_zero {n den : ℕ} {nodes : List PLNode} (hvalid : PLValid n nodes) :
    plWitness n den nodes 0 = 0 := by
  induction nodes with
  | nil => simp [plWitness]
  | cons p ps ih =>
      have hp := hvalid p (List.mem_cons_self)
      have hps : PLValid n ps := fun q hq => hvalid q (List.mem_cons_of_mem _ hq)
      simp only [plWitness, List.map_cons, List.sum_cons, gridTent_zero hp.1, mul_zero,
        zero_add] at ⊢
      exact ih hps

/-- Exact integral of every sparse nonnegative witness. -/
theorem plWitness_integral {n den : ℕ} {nodes : List PLNode}
    (hn : 0 < n) (hden : 0 < den) (hvalid : PLValid n nodes) :
    (∫ t in (0 : ℝ)..1, plWitness n den nodes t) =
      (plMass nodes : ℝ) / ((n : ℝ) * den) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hden0 : (den : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hden
  induction nodes with
  | nil => simp [plWitness, plMass]
  | cons p ps ih =>
      have hp := hvalid p (List.mem_cons_self)
      have hps : PLValid n ps := fun q hq => hvalid q (List.mem_cons_of_mem _ hq)
      have hpi := ((gridTent_lipschitz n p.index).continuous.intervalIntegrable
        (μ := volume) 0 1).const_mul
        ((p.numerator : ℝ) / den)
      have hpsi := (plWitness_continuous n den ps).intervalIntegrable (μ := volume) 0 1
      change (∫ t in (0 : ℝ)..1,
        ((p.numerator : ℝ) / den) * gridTent n p.index t + plWitness n den ps t) = _
      rw [intervalIntegral.integral_add hpi hpsi, intervalIntegral.integral_const_mul,
        gridTent_integral hn hp.1 hp.2, ih hps]
      simp only [plMass, List.map_cons, List.sum_cons, Nat.cast_add]
      field_simp

/-- Absolute values introduce no numerical approximation: the witnesses are nonnegative. -/
theorem plWitness_integral_abs {n den : ℕ} {nodes : List PLNode}
    (hn : 0 < n) (hden : 0 < den) (hvalid : PLValid n nodes) :
    (∫ t in (0 : ℝ)..1, |plWitness n den nodes t|) =
      (plMass nodes : ℝ) / ((n : ℝ) * den) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, plWitness n den nodes t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact abs_of_nonneg (plWitness_nonneg n den nodes t)
    _ = _ := plWitness_integral hn hden hvalid

end

end

end ErdosOverlap
