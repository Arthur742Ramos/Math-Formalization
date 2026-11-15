/-
Copyright (c) 2026. Released under the BSD-3-Clause license.

Scalar inequalities for the boundary-capacity and odd-profile arguments in
Erdős' minimum-overlap problem. All results in this file are universal real
inequalities; no numerical certificate or discretization is assumed.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Pointwise overlap inequalities

This file proves the exact boundary-pair defect, a four-overlap linear bound,
and the box-constrained scalar conjugate used by the continuous odd-profile
dual. The finite numerical certificate is logically separate from this file.
-/

namespace ErdosOverlap

public section

/-- The deficit in the boundary-pair estimate splits into binarity defects
and the square of the complementarity defect. -/
theorem boundary_pair_defect_identity (a b : ℝ) :
    1 - (a + b - 2 * a * b) =
      a * (1 - a) + b * (1 - b) + (a + b - 1) ^ 2 := by
  ring

/-- A second useful exact form of the boundary-pair defect. -/
theorem boundary_pair_defect_product_identity (a b : ℝ) :
    1 - (a + b - 2 * a * b) = a * b + (1 - a) * (1 - b) := by
  ring

/-- Two values in the unit interval have boundary-pair overlap at most one. -/
theorem boundary_pair_le_one {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a + b - 2 * a * b ≤ 1 := by
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab' : 0 ≤ (1 - a) * (1 - b) :=
    mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
  nlinarith [boundary_pair_defect_product_identity a b]

/-- Equality forces the two entries to be complementary binary values. -/
theorem boundary_pair_eq_one_iff {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a + b - 2 * a * b = 1 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
    have hab' : 0 ≤ (1 - a) * (1 - b) :=
      mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
    have hab0 : a * b = 0 := by
      nlinarith [boundary_pair_defect_product_identity a b]
    rcases mul_eq_zero.mp hab0 with ha | hb
    · left
      exact ⟨ha, by nlinarith⟩
    · right
      exact ⟨by nlinarith, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- The boundary deficit quantitatively controls both binarity defects and
the square of the complementarity defect. -/
theorem boundary_pair_defect_controls {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * (1 - a) ≤ 1 - (a + b - 2 * a * b) ∧
      b * (1 - b) ≤ 1 - (a + b - 2 * a * b) ∧
      (a + b - 1) ^ 2 ≤ 1 - (a + b - 2 * a * b) := by
  have ha : 0 ≤ a * (1 - a) := mul_nonneg ha0 (sub_nonneg.mpr ha1)
  have hb : 0 ≤ b * (1 - b) := mul_nonneg hb0 (sub_nonneg.mpr hb1)
  have hs := sq_nonneg (a + b - 1)
  rw [boundary_pair_defect_identity]
  constructor
  · linarith
  constructor <;> linarith

/-- A signed linear functional on the segment `[u, 2*M-u]`. -/
theorem linear_segment_upper_bound {A s M u : ℝ}
    (hslo : u ≤ s) (hshi : s ≤ 2 * M - u) :
    A * s ≤ 2 * M * max A 0 - |A| * u := by
  by_cases hA : 0 ≤ A
  · rw [max_eq_left hA, abs_of_nonneg hA]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hshi)]
  · have hA' : A ≤ 0 := le_of_not_ge hA
    rw [max_eq_right hA', abs_of_nonpos hA']
    nlinarith [mul_nonneg (neg_nonneg.mpr hA') (sub_nonneg.mpr hslo)]

/-- The same segment bound with the additional boundary cap `V ≤ t`.
The positive-part correction is exact at the corresponding endpoint. -/
theorem linear_segment_cap_upper_bound {B V M t u : ℝ}
    (hVlo : u ≤ V) (hVhi : V ≤ 2 * M - u) (hVt : V ≤ t) :
    B * V ≤ 2 * M * max B 0 - |B| * u -
      max B 0 * max (2 * M - t - u) 0 := by
  by_cases hB : 0 ≤ B
  · rw [max_eq_left hB, abs_of_nonneg hB]
    by_cases ht : 0 ≤ 2 * M - t - u
    · rw [max_eq_left ht]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hVt)]
    · rw [max_eq_right (le_of_not_ge ht)]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hVhi)]
  · have hB' : B ≤ 0 := le_of_not_ge hB
    rw [max_eq_right hB', abs_of_nonpos hB']
    nlinarith [mul_nonneg (neg_nonneg.mpr hB') (sub_nonneg.mpr hVlo)]

/-- The quartet inequality used in the boundary-capacity improvement.
No sign assumption on either kernel coefficient is required. -/
theorem quartet_upper_bound {A B s V M t u : ℝ}
    (_hu : 0 ≤ u) (hslo : u ≤ s) (hshi : s ≤ 2 * M - u)
    (hVlo : u ≤ V) (hVhi : V ≤ min (2 * M - u) t) :
    A * s + B * V ≤
      2 * M * (max A 0 + max B 0) -
        ((|A| + |B|) * u + max B 0 * max (2 * M - t - u) 0) := by
  have hs := linear_segment_upper_bound (A := A) hslo hshi
  have hV := linear_segment_cap_upper_bound (B := B) hVlo
    (hVhi.trans (min_le_left _ _)) (hVhi.trans (min_le_right _ _))
  nlinarith

/-- The even convex cost in the odd-profile dual. -/
@[expose] def profileCost (b c L z : ℝ) : ℝ :=
  c * |z| + b * max (L - |z|) 0

/-- The exact minimum of `profileCost b c L z - lam*z` on `|z| ≤ U`
when `0 ≤ b ≤ c` and `L,U ≥ 0`. -/
@[expose] def profileConjugate (b c L U lam : ℝ) : ℝ :=
  b * L - min U L * max (|lam| - c + b) 0 -
    (U - min U L) * max (|lam| - c) 0

/-- A signed coefficient on a nonnegative bounded interval is controlled by
its positive part at the upper endpoint. -/
theorem mul_le_positive_part_mul {d x T : ℝ}
    (hx : 0 ≤ x) (hTx : x ≤ T) : d * x ≤ max d 0 * T := by
  exact (mul_le_mul_of_nonneg_right (le_max_left d 0) hx).trans
    (mul_le_mul_of_nonneg_left hTx (le_max_right d 0))

/-- Algebraic decomposition into the two slopes of the radial cost. -/
theorem radial_cost_decomposition (b c L x ell : ℝ) :
    c * x + b * max (L - x) 0 - ell * x =
      b * L - (ell - c + b) * min x L -
        (ell - c) * max (x - L) 0 := by
  by_cases h : x ≤ L
  · rw [max_eq_left (sub_nonneg.mpr h), min_eq_left h,
      max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h' : L ≤ x := le_of_not_ge h
    rw [max_eq_right (sub_nonpos.mpr h'), min_eq_right h',
      max_eq_left (sub_nonneg.mpr h')]
    ring

/-- The length of the upper radial interval. -/
theorem sub_min_eq_positive_part (U L : ℝ) :
    U - min U L = max (U - L) 0 := by
  by_cases h : U ≤ L
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · have h' : L ≤ U := le_of_not_ge h
    rw [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]

/-- A stronger hypothesis-free-in-`b,c` version of the scalar lower bound.
Convexity of the cost is needed for attainment, not for this inequality. -/
theorem profileConjugate_le_cost_sub_linear_of_abs_le
    {b c L U lam z : ℝ} (hL : 0 ≤ L) (_hU : 0 ≤ U) (hz : |z| ≤ U) :
    profileConjugate b c L U lam ≤ profileCost b c L z - lam * z := by
  have hx0 : 0 ≤ min |z| L := le_min (abs_nonneg z) hL
  have hxU : min |z| L ≤ min U L := min_le_min hz le_rfl
  have hy0 : 0 ≤ max (|z| - L) 0 := le_max_right _ _
  have hyU : max (|z| - L) 0 ≤ U - min U L := by
    rw [sub_min_eq_positive_part]
    exact max_le_max (sub_le_sub_right hz L) le_rfl
  have hx := mul_le_positive_part_mul (d := |lam| - c + b) hx0 hxU
  have hy := mul_le_positive_part_mul (d := |lam| - c) hy0 hyU
  have hlin : lam * z ≤ |lam| * |z| := by
    calc
      lam * z ≤ |lam * z| := le_abs_self _
      _ = |lam| * |z| := abs_mul _ _
  have hid := radial_cost_decomposition b c L |z| |lam|
  unfold profileConjugate profileCost
  nlinarith

/-- The universal scalar inequality used by the continuous dual. -/
theorem profileConjugate_le_cost_sub_linear
    {b c L U lam z : ℝ} (_hb : 0 ≤ b) (_hbc : b ≤ c)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hz : |z| ≤ U) :
    profileConjugate b c L U lam ≤ profileCost b c L z - lam * z := by
  exact profileConjugate_le_cost_sub_linear_of_abs_le hL hU hz

/-- The point of radius `r` whose sign agrees with the linear coefficient.
At `lam = 0` the positive choice is used. -/
@[expose] noncomputable def signedRadius (lam r : ℝ) : ℝ := if 0 ≤ lam then r else -r

theorem abs_signedRadius {lam r : ℝ} (hr : 0 ≤ r) :
    |signedRadius lam r| = r := by
  unfold signedRadius
  split_ifs
  · exact abs_of_nonneg hr
  · rw [abs_neg, abs_of_nonneg hr]

theorem linear_signedRadius (lam r : ℝ) :
    lam * signedRadius lam r = |lam| * r := by
  by_cases h : 0 ≤ lam
  · simp [signedRadius, h, abs_of_nonneg h]
  · rw [signedRadius, ite_eq_right h, abs_of_nonpos (le_of_not_ge h)]
    ring

theorem cost_sub_linear_signedRadius (b c L lam r : ℝ) (hr : 0 ≤ r) :
    profileCost b c L (signedRadius lam r) - lam * signedRadius lam r =
      c * r + b * max (L - r) 0 - |lam| * r := by
  unfold profileCost
  rw [abs_signedRadius hr, linear_signedRadius]

/-- If the linear coefficient is below the first slope, zero attains the
scalar minimum. -/
theorem profileConjugate_attained_at_zero {b c L U lam : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hsmall : |lam| ≤ c - b) :
    profileCost b c L 0 - lam * 0 = profileConjugate b c L U lam := by
  have hfirst : |lam| - c + b ≤ 0 := by linarith
  have hsecond : |lam| - c ≤ 0 := by linarith
  simp [profileCost, profileConjugate, max_eq_left hL,
    max_eq_right hfirst, max_eq_right hsecond]

/-- Between the two slopes, the first breakpoint attains the minimum. -/
theorem profileConjugate_attained_at_min {b c L U lam : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hlower : c - b ≤ |lam|) (hupper : |lam| ≤ c) :
    profileCost b c L (signedRadius lam (min U L)) -
      lam * signedRadius lam (min U L) = profileConjugate b c L U lam := by
  have hfirst : 0 ≤ |lam| - c + b := by linarith
  have hsecond : |lam| - c ≤ 0 := by linarith
  rw [cost_sub_linear_signedRadius b c L lam (min U L) (le_min hU hL)]
  unfold profileConjugate
  rw [max_eq_left (sub_nonneg.mpr (min_le_right U L)),
    max_eq_left hfirst, max_eq_right hsecond]
  ring

/-- Above the second slope, the outer endpoint attains the minimum. -/
theorem profileConjugate_attained_at_upper {b c L U lam : ℝ}
    (hb : 0 ≤ b) (hU : 0 ≤ U) (hlarge : c ≤ |lam|) :
    profileCost b c L (signedRadius lam U) - lam * signedRadius lam U =
      profileConjugate b c L U lam := by
  have hfirst : 0 ≤ |lam| - c + b := by linarith
  have hsecond : 0 ≤ |lam| - c := by linarith
  rw [cost_sub_linear_signedRadius b c L lam U hU,
    radial_cost_decomposition]
  unfold profileConjugate
  rw [max_eq_left hfirst, max_eq_left hsecond,
    ← sub_min_eq_positive_part]
  ring

/-- One of three explicit signed candidates always attains the scalar bound.
The assertion includes the candidate's admissibility, not just its value. -/
theorem profileConjugate_exists_attainer {b c L U lam : ℝ}
    (hb : 0 ≤ b) (_hbc : b ≤ c) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    ∃ z : ℝ, |z| ≤ U ∧
      (z = 0 ∨ z = signedRadius lam (min U L) ∨ z = signedRadius lam U) ∧
      profileCost b c L z - lam * z = profileConjugate b c L U lam := by
  by_cases hsmall : |lam| ≤ c - b
  · refine ⟨0, ?_, Or.inl rfl, ?_⟩
    · simpa using hU
    · exact profileConjugate_attained_at_zero hb hL hsmall
  · by_cases hmiddle : |lam| ≤ c
    · refine ⟨signedRadius lam (min U L), ?_, Or.inr (Or.inl rfl), ?_⟩
      · rw [abs_signedRadius (le_min hU hL)]
        exact min_le_left _ _
      · exact profileConjugate_attained_at_min hL hU (le_of_not_ge hsmall) hmiddle
    · refine ⟨signedRadius lam U, ?_, Or.inr (Or.inr rfl), ?_⟩
      · rw [abs_signedRadius hU]
      · exact profileConjugate_attained_at_upper hb hU (le_of_not_ge hmiddle)

/-- Exact scalar conjugacy: the displayed number is both a universal lower
bound on the box and an attained value at an explicitly listed candidate. -/
theorem profileConjugate_exact {b c L U lam : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    (∀ z : ℝ, |z| ≤ U →
      profileConjugate b c L U lam ≤ profileCost b c L z - lam * z) ∧
    (∃ z : ℝ, |z| ≤ U ∧
      (z = 0 ∨ z = signedRadius lam (min U L) ∨ z = signedRadius lam U) ∧
      profileCost b c L z - lam * z = profileConjugate b c L U lam) := by
  exact ⟨fun _ hz => profileConjugate_le_cost_sub_linear hb hbc hL hU hz,
    profileConjugate_exists_attainer hb hbc hL hU⟩

end

end ErdosOverlap
