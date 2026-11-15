/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafCertificateData

/-!
# Endpoint-certified capacity branches on a native integration leaf

Midpoints choose an executable affine formula. The endpoint checks prove
that the chosen formula agrees with each max/min on the entire real leaf.
-/

@[expose] public section

namespace ErdosOverlap.Native6Leaves

open Numerics MeasureTheory Set

theorem affineEval_cast (a : RationalAffine) (t : ℚ) :
    (affineEval a t : ℝ) = a.value (t : ℝ) := by
  simp only [affineEval, RationalAffine.value, Rat.cast_add, Rat.cast_mul]

theorem affineLeCheck_sound {a b : RationalAffine} {lo hi : ℚ}
    (hc : affineLeCheck a b lo hi = true) {t : ℝ}
    (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) : a.value t ≤ b.value t := by
  have he := of_decide_eq_true hc
  have hl : a.value (lo : ℝ) ≤ b.value (lo : ℝ) := by
    rw [← affineEval_cast, ← affineEval_cast]
    exact (Rat.cast_le (K := ℝ)).2 he.1
  have hh : a.value (hi : ℝ) ≤ b.value (hi : ℝ) := by
    rw [← affineEval_cast, ← affineEval_cast]
    exact (Rat.cast_le (K := ℝ)).2 he.2
  simp only [RationalAffine.value] at hl hh ⊢
  have h := affine_nonneg_on_interval
    (α := (b.slope : ℝ)-(a.slope : ℝ))
    (β := (b.constant : ℝ)-(a.constant : ℝ)) ht
    (by linarith) (by linarith)
  linarith

theorem capacities_L {lo hi : ℚ} (hc : capacityCheck lo hi = true)
    {t : ℝ} (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (capacities lo hi).L.value t = max (2*(auxiliaryLevel : ℝ)-t) 0 := by
  simp only [capacityCheck, Bool.and_eq_true] at hc
  have hL := hc.1.1
  have hdef : (capacities lo hi).L =
      if (lo+hi)/2 < 2*auxiliaryLevel then ⟨2*auxiliaryLevel,-1⟩ else ⟨0,0⟩ := rfl
  rw [hdef]
  split_ifs with hmid
  · simp only [hmid, ite_true, decide_eq_true_eq] at hL
    have hb : (hi : ℝ) ≤ 2*(auxiliaryLevel : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hL
    rw [max_eq_left (by linarith [ht.2])]
    simp only [RationalAffine.value, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one]
    ring
  · simp only [hmid, ite_false, decide_eq_true_eq] at hL
    have hb : 2*(auxiliaryLevel : ℝ) ≤ (lo : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hL
    rw [max_eq_right (by linarith [ht.1])]
    simp [RationalAffine.value]

theorem capacities_U {lo hi : ℚ} (hc : capacityCheck lo hi = true)
    {t : ℝ} (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (capacities lo hi).U.value t = min t (boxCap : ℝ) := by
  simp only [capacityCheck, Bool.and_eq_true] at hc
  have hU := hc.1.2
  have hdef : (capacities lo hi).U =
      if (lo+hi)/2 < boxCap then ⟨0,1⟩ else ⟨boxCap,0⟩ := rfl
  rw [hdef]
  split_ifs with hmid
  · simp only [hmid, ite_true, decide_eq_true_eq] at hU
    have hb : (hi : ℝ) ≤ (boxCap : ℝ) := (Rat.cast_le (K := ℝ)).2 hU
    rw [min_eq_left (ht.2.trans hb)]
    simp [RationalAffine.value]
  · simp only [hmid, ite_false, decide_eq_true_eq] at hU
    have hb : (boxCap : ℝ) ≤ (lo : ℝ) := (Rat.cast_le (K := ℝ)).2 hU
    rw [min_eq_right (hb.trans ht.1)]
    simp [RationalAffine.value]

theorem capacities_K {lo hi : ℚ} (hc : capacityCheck lo hi = true)
    {t : ℝ} (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (capacities lo hi).K.value t =
      min ((capacities lo hi).U.value t) ((capacities lo hi).L.value t) := by
  simp only [capacityCheck, Bool.and_eq_true] at hc
  have hK := hc.2
  have hdef : (capacities lo hi).K =
      if affineEval (capacities lo hi).L ((lo+hi)/2) ≤
          affineEval (capacities lo hi).U ((lo+hi)/2)
      then (capacities lo hi).L else (capacities lo hi).U := rfl
  rw [hdef]
  split_ifs with hmid
  · simp only [hmid, ite_true] at hK
    exact (min_eq_right (affineLeCheck_sound hK ht)).symm
  · simp only [hmid, ite_false] at hK
    exact (min_eq_left (affineLeCheck_sound hK ht)).symm

theorem capacities_V (lo hi : ℚ) (t : ℝ) :
    (capacities lo hi).V.value t =
      (capacities lo hi).U.value t-(capacities lo hi).K.value t := by
  change ((capacities lo hi).U.sub (capacities lo hi).K).value t = _
  simp only [RationalAffine.sub, RationalAffine.value, Rat.cast_sub]
  ring

theorem capacity_parameter_bounds :
    0 ≤ (auxiliaryLevel : ℝ) ∧ 2*(auxiliaryLevel : ℝ) ≤ 1 ∧
    0 ≤ (boxCap : ℝ) ∧ (boxCap : ℝ) ≤ 1 := by
  norm_num [auxiliaryLevel, boxCap]

theorem capacities_bounds {lo hi : ℚ} (hc : capacityCheck lo hi = true)
    {t : ℝ} (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) (ht01 : t ∈ Icc (0 : ℝ) 1) :
    (0 ≤ (capacities lo hi).L.value t ∧ (capacities lo hi).L.value t ≤ 1) ∧
    (0 ≤ (capacities lo hi).U.value t ∧ (capacities lo hi).U.value t ≤ 1) := by
  rw [capacities_L hc ht, capacities_U hc ht]
  refine ⟨⟨le_max_right _ _, max_le ?_ zero_le_one⟩,
    ⟨le_min ht01.1 capacity_parameter_bounds.2.2.1,
      (min_le_left _ _).trans ht01.2⟩⟩
  linarith [capacity_parameter_bounds.2.1, ht01.1]

end ErdosOverlap.Native6Leaves
