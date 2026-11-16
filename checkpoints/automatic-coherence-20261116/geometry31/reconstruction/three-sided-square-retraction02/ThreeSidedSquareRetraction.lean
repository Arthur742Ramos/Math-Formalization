module
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-! SOURCE ONLY / UNCOMPILED.
An explicit retraction of the square onto its bottom and two vertical sides.
This module does not construct a square filler or a cylinder equivalence. -/
@[expose] public section
noncomputable section
open scoped Topology

namespace AutomaticCoherence.ThreeSidedSquareRetraction01

abbrev I := unitInterval

def scale (p : I × I) : ℝ :=
  max (1 - (p.1 : ℝ) / 2) |2 * (p.2 : ℝ) - 1|

lemma time_le_scale (p : I × I) : 1 - (p.1 : ℝ) / 2 ≤ scale p :=
  le_max_left _ _

lemma abs_le_scale (p : I × I) : |2 * (p.2 : ℝ) - 1| ≤ scale p :=
  le_max_right _ _

lemma half_le_scale (p : I × I) : (1 : ℝ) / 2 ≤ scale p := by
  have h := time_le_scale p
  have ht := p.1.property.2
  linarith

lemma scale_pos (p : I × I) : 0 < scale p := by
  have h := half_le_scale p
  linarith

lemma scale_ne_zero (p : I × I) : scale p ≠ 0 := ne_of_gt (scale_pos p)

lemma scale_le_one (p : I × I) : scale p ≤ 1 := by
  apply max_le
  · have ht := p.1.property.1
    linarith
  · apply abs_le.mpr
    have hs0 := p.2.property.1
    have hs1 := p.2.property.2
    constructor <;> linarith

def timeCoord (p : I × I) : ℝ := 2 - (2 - (p.1 : ℝ)) / scale p
def pathCoord (p : I × I) : ℝ := (1 + (2 * (p.2 : ℝ) - 1) / scale p) / 2

lemma timeCoord_nonneg (p : I × I) : 0 ≤ timeCoord p := by
  have h : (2 - (p.1 : ℝ)) / scale p ≤ 2 :=
    (div_le_iff₀ (scale_pos p)).2 (by
      have hd := time_le_scale p
      linarith)
  dsimp [timeCoord]
  linarith

lemma timeCoord_le_time (p : I × I) : timeCoord p ≤ (p.1 : ℝ) := by
  have ht : 0 ≤ 2 - (p.1 : ℝ) := by
    have h := p.1.property.2
    linarith
  have h : 2 - (p.1 : ℝ) ≤ (2 - (p.1 : ℝ)) / scale p :=
    (le_div_iff₀ (scale_pos p)).2 (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (scale_le_one p) ht)
  dsimp [timeCoord]
  linarith

lemma timeCoord_mem (p : I × I) : timeCoord p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨timeCoord_nonneg p, (timeCoord_le_time p).trans p.1.property.2⟩

lemma pathCoord_mem (p : I × I) : pathCoord p ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := abs_le.mp (abs_le_scale p)
  have hl : (-1 : ℝ) ≤ (2 * (p.2 : ℝ) - 1) / scale p :=
    (le_div_iff₀ (scale_pos p)).2 (by linarith [hs.1])
  have hu : (2 * (p.2 : ℝ) - 1) / scale p ≤ 1 :=
    (div_le_iff₀ (scale_pos p)).2 (by linarith [hs.2])
  dsimp [pathCoord]
  constructor <;> linarith

lemma continuous_scale : Continuous scale := by unfold scale; fun_prop

lemma continuous_timeCoord : Continuous timeCoord := by
  unfold timeCoord
  exact continuous_const.sub
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
      continuous_scale scale_ne_zero)

lemma continuous_pathCoord : Continuous pathCoord := by
  unfold pathCoord
  have h : Continuous (fun p : I × I => 2 * (p.2 : ℝ) - 1) := by fun_prop
  exact (continuous_const.add (h.div continuous_scale scale_ne_zero)).div_const 2

/-- The displayed formulas define a genuine continuous self-map of the square. -/
def retract : C(I × I, I × I) where
  toFun p := (⟨timeCoord p, timeCoord_mem p⟩, ⟨pathCoord p, pathCoord_mem p⟩)
  continuous_toFun :=
    (continuous_timeCoord.subtype_mk timeCoord_mem).prodMk
      (continuous_pathCoord.subtype_mk pathCoord_mem)

lemma scale_bottom (s : I) : scale (0, s) = 1 := by
  have h : |2 * (s : ℝ) - 1| ≤ 1 := by
    have hs0 := s.property.1
    have hs1 := s.property.2
    apply abs_le.mpr
    constructor <;> linarith
  norm_num [scale, max_eq_left h]

lemma scale_left (t : I) : scale (t, 0) = 1 := by
  have h : 1 - (t : ℝ) / 2 ≤ 1 := by
    have ht := t.property.1
    linarith
  norm_num [scale, max_eq_right h]

lemma scale_right (t : I) : scale (t, 1) = 1 := by
  have h : 1 - (t : ℝ) / 2 ≤ 1 := by
    have ht := t.property.1
    linarith
  norm_num [scale, max_eq_right h]

lemma retract_bottom (s : I) : retract (0, s) = (0, s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change timeCoord (0, s) = 0
    rw [timeCoord, scale_bottom]
    norm_num
  · change pathCoord (0, s) = (s : ℝ)
    rw [pathCoord, scale_bottom]
    ring

lemma retract_left (t : I) : retract (t, 0) = (t, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change timeCoord (t, 0) = (t : ℝ)
    rw [timeCoord, scale_left]
    ring
  · change pathCoord (t, 0) = 0
    rw [pathCoord, scale_left]
    norm_num

lemma retract_right (t : I) : retract (t, 1) = (t, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change timeCoord (t, 1) = (t : ℝ)
    rw [timeCoord, scale_right]
    ring
  · change pathCoord (t, 1) = 1
    rw [pathCoord, scale_right]
    norm_num

def ThreeSides : Set (I × I) := {p | p.1 = 0 ∨ p.2 = 0 ∨ p.2 = 1}

lemma retract_mem (p : I × I) : retract p ∈ ThreeSides := by
  change (retract p).1 = 0 ∨ (retract p).2 = 0 ∨ (retract p).2 = 1
  by_cases h : |2 * (p.2 : ℝ) - 1| ≤ 1 - (p.1 : ℝ) / 2
  · left
    apply Subtype.ext
    change timeCoord p = 0
    have he : scale p = 1 - (p.1 : ℝ) / 2 := max_eq_left h
    have hn : 1 - (p.1 : ℝ) / 2 ≠ 0 := by
      have ht := p.1.property.2
      linarith
    have hd : (2 - (p.1 : ℝ)) / (1 - (p.1 : ℝ) / 2) = 2 :=
      (div_eq_iff hn).2 (by ring)
    rw [timeCoord, he, hd]
    norm_num
  · right
    have he : scale p = |2 * (p.2 : ℝ) - 1| :=
      max_eq_right (lt_of_not_ge h).le
    by_cases hs : 0 ≤ 2 * (p.2 : ℝ) - 1
    · right
      apply Subtype.ext
      change pathCoord p = 1
      have hn : 2 * (p.2 : ℝ) - 1 ≠ 0 := by
        have hp := scale_pos p
        rw [he, abs_of_nonneg hs] at hp
        exact ne_of_gt hp
      rw [pathCoord, he, abs_of_nonneg hs]
      field_simp [hn] <;> ring
    · left
      apply Subtype.ext
      change pathCoord p = 0
      have hn : -(2 * (p.2 : ℝ) - 1) ≠ 0 := by
        have hh := lt_of_not_ge hs
        linarith
      have hd : (2 * (p.2 : ℝ) - 1) / (-(2 * (p.2 : ℝ) - 1)) = -1 :=
        (div_eq_iff hn).2 (by ring)
      rw [pathCoord, he, abs_of_neg (lt_of_not_ge hs), hd]
      norm_num

lemma retract_fixed (p : I × I) (hp : p ∈ ThreeSides) : retract p = p := by
  rcases p with ⟨t, s⟩
  change t = 0 ∨ s = 0 ∨ s = 1 at hp
  rcases hp with ht | hs | hs
  · subst t
    exact retract_bottom s
  · subst s
    exact retract_left t
  · subst s
    exact retract_right t

/-- Actual codomain restriction; the image condition is proved, not a premise. -/
def edgeRetract : C(I × I, ThreeSides) where
  toFun p := ⟨retract p, retract_mem p⟩
  continuous_toFun := retract.continuous.subtype_mk retract_mem

lemma edgeRetract_fixed (p : ThreeSides) : edgeRetract p.val = p :=
  Subtype.ext (retract_fixed p.val p.property)

end AutomaticCoherence.ThreeSidedSquareRetraction01
