module

public import ErdosOverlap.Numerics.CellBounds
public import LeanCert.Core.IntervalRat.Taylor

/-! # Compact fixed-point interval arithmetic

The executable data consists only of two integers. Soundness is proved
separately, so kernel evaluation does not carry nested validity proofs through
millions of arithmetic operations. All intervals use the exact scale 2^128.
-/

namespace ErdosOverlap.Numerics

open LeanCert.Core

@[expose] public section

def fixedScale : ℤ := 340282366920938463463374607431768211456

theorem fixedScale_eq_two_pow : fixedScale = 2^128 := by norm_num [fixedScale]

theorem fixedScale_pos : 0 < fixedScale := by norm_num [fixedScale]

theorem fixedScale_real_pos : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos

structure FixedBox where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace FixedBox

noncomputable def Contains (I : FixedBox) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x*(fixedScale : ℝ) ∧ x*(fixedScale : ℝ) ≤ (I.hi : ℝ)

noncomputable instance : Membership ℝ FixedBox := ⟨Contains⟩

def add (I J : FixedBox) : FixedBox := ⟨I.lo+J.lo, I.hi+J.hi⟩
def neg (I : FixedBox) : FixedBox := ⟨-I.hi, -I.lo⟩
def sub (I J : FixedBox) : FixedBox := I.add J.neg

theorem mem_add {x y : ℝ} {I J : FixedBox} (hx : x ∈ I) (hy : y ∈ J) :
    x+y ∈ I.add J := by
  change (I.lo : ℝ) ≤ x*(fixedScale : ℝ) ∧ x*(fixedScale : ℝ) ≤ I.hi at hx
  change (J.lo : ℝ) ≤ y*(fixedScale : ℝ) ∧ y*(fixedScale : ℝ) ≤ J.hi at hy
  change ((I.lo+J.lo : ℤ) : ℝ) ≤ (x+y)*fixedScale ∧ (x+y)*fixedScale ≤ ((I.hi+J.hi : ℤ) : ℝ)
  push_cast
  constructor <;> nlinarith

theorem mem_neg {x : ℝ} {I : FixedBox} (hx : x ∈ I) : -x ∈ I.neg := by
  change (I.lo : ℝ) ≤ x*(fixedScale : ℝ) ∧ x*(fixedScale : ℝ) ≤ I.hi at hx
  change ((-I.hi : ℤ) : ℝ) ≤ (-x)*fixedScale ∧ (-x)*fixedScale ≤ ((-I.lo : ℤ) : ℝ)
  push_cast
  constructor <;> nlinarith

theorem mem_sub {x y : ℝ} {I J : FixedBox} (hx : x ∈ I) (hy : y ∈ J) :
    x-y ∈ I.sub J := by
  convert! mem_add hx (mem_neg hy) using 1

def minProduct (I J : FixedBox) : ℤ :=
  min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi))

def maxProduct (I J : FixedBox) : ℤ :=
  max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))

def mul (I J : FixedBox) : FixedBox :=
  ⟨I.minProduct J / fixedScale, -((-I.maxProduct J)/fixedScale)⟩

theorem bilinear_lower {a b c d x y z : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : z ≤ a*c) (had : z ≤ a*d) (hbc : z ≤ b*c) (hbd : z ≤ b*d) :
    z ≤ x*y := by
  have hc : 0 ≤ c*x-z := affine_nonneg_on_interval hx (by nlinarith) (by nlinarith)
  have hd : 0 ≤ d*x-z := affine_nonneg_on_interval hx (by nlinarith) (by nlinarith)
  have h := affine_nonneg_on_interval (α := x) (β := -z) hy (by nlinarith) (by nlinarith)
  linarith

theorem bilinear_upper {a b c d x y z : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a*c ≤ z) (had : a*d ≤ z) (hbc : b*c ≤ z) (hbd : b*d ≤ z) :
    x*y ≤ z := by
  have hc : 0 ≤ (-c)*x+z := affine_nonneg_on_interval hx (by nlinarith) (by nlinarith)
  have hd : 0 ≤ (-d)*x+z := affine_nonneg_on_interval hx (by nlinarith) (by nlinarith)
  have h := affine_nonneg_on_interval (α := -x) (β := z) hy (by nlinarith) (by nlinarith)
  linarith

theorem floor_div_mul_le (n : ℤ) : (n/fixedScale)*fixedScale ≤ n := by
  exact Int.ediv_mul_le n (ne_of_gt fixedScale_pos)

theorem le_ceil_div_mul (n : ℤ) : n ≤ (-((-n)/fixedScale))*fixedScale := by
  have h := floor_div_mul_le (-n)
  nlinarith

theorem mem_mul {x y : ℝ} {I J : FixedBox} (hx : x ∈ I) (hy : y ∈ J) :
    x*y ∈ I.mul J := by
  change (I.lo : ℝ) ≤ x*(fixedScale : ℝ) ∧ x*(fixedScale : ℝ) ≤ I.hi at hx
  change (J.lo : ℝ) ≤ y*(fixedScale : ℝ) ∧ y*(fixedScale : ℝ) ≤ J.hi at hy
  have hmin : (I.minProduct J : ℝ) ≤ (x*fixedScale)*(y*fixedScale) := by
    apply bilinear_lower hx hy <;> simp only [minProduct, Int.cast_min, Int.cast_mul]
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmax : (x*fixedScale)*(y*fixedScale) ≤ (I.maxProduct J : ℝ) := by
    apply bilinear_upper hx hy <;> simp only [maxProduct, Int.cast_max, Int.cast_mul]
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hlo : ((I.minProduct J/fixedScale : ℤ) : ℝ)*(fixedScale : ℝ) ≤ I.minProduct J := by
    exact_mod_cast floor_div_mul_le (I.minProduct J)
  have hhi : (I.maxProduct J : ℝ) ≤ ((-((-I.maxProduct J)/fixedScale) : ℤ) : ℝ)*fixedScale := by
    exact_mod_cast le_ceil_div_mul (I.maxProduct J)
  change ((I.minProduct J/fixedScale : ℤ) : ℝ) ≤ x*y*fixedScale ∧
    x*y*fixedScale ≤ ((-((-I.maxProduct J)/fixedScale) : ℤ) : ℝ)
  constructor
  · apply (mul_le_mul_iff_right₀ fixedScale_real_pos).mp
    nlinarith [hlo.trans hmin]
  · apply (mul_le_mul_iff_right₀ fixedScale_real_pos).mp
    nlinarith [hmax.trans hhi]

def ofRat (q : ℚ) : FixedBox :=
  ⟨(q*(fixedScale : ℚ)).floor, -((-q*(fixedScale : ℚ)).floor)⟩

theorem mem_ofRat (q : ℚ) : (q : ℝ) ∈ ofRat q := by
  have hlo : ((q*(fixedScale : ℚ)).floor : ℚ) ≤ q*fixedScale := Int.floor_le _
  have hhi : ((-q*(fixedScale : ℚ)).floor : ℚ) ≤ -q*fixedScale := Int.floor_le _
  change (((q*(fixedScale : ℚ)).floor : ℤ) : ℝ) ≤ (q : ℝ)*fixedScale ∧
    (q : ℝ)*fixedScale ≤ ((-((-q*(fixedScale : ℚ)).floor) : ℤ) : ℝ)
  constructor
  · exact_mod_cast hlo
  · have h : (((-q*(fixedScale : ℚ)).floor : ℤ) : ℝ) ≤ -(q : ℝ)*fixedScale := by
      exact_mod_cast hhi
    push_cast
    nlinarith

def ofIntervalRat (I : IntervalRat) : FixedBox := ⟨(ofRat I.lo).lo, (ofRat I.hi).hi⟩

theorem mem_ofIntervalRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x ∈ ofIntervalRat I := by
  have hl := (mem_ofRat I.lo).1
  have hh := (mem_ofRat I.hi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right hx.1 fixedScale_real_pos.le),
    (mul_le_mul_of_nonneg_right hx.2 fixedScale_real_pos.le).trans hh⟩

def scaleInt (I : FixedBox) (k : ℤ) : FixedBox :=
  if 0 ≤ k then ⟨k*I.lo, k*I.hi⟩ else ⟨k*I.hi, k*I.lo⟩

theorem mem_scaleInt {x : ℝ} {I : FixedBox} (hx : x ∈ I) (k : ℤ) :
    (k : ℝ)*x ∈ I.scaleInt k := by
  change (I.lo : ℝ) ≤ x*(fixedScale : ℝ) ∧ x*(fixedScale : ℝ) ≤ I.hi at hx
  unfold scaleInt
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    constructor <;> push_cast
    · nlinarith [mul_le_mul_of_nonneg_left hx.1 hk']
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 hk']
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hk
    constructor <;> push_cast
    · nlinarith [mul_le_mul_of_nonpos_left hx.2 hk']
    · nlinarith [mul_le_mul_of_nonpos_left hx.1 hk']

def upperBoundedBy (I : FixedBox) (q : ℚ) : Bool := decide ((I.hi : ℚ) ≤ q*fixedScale)
def lowerBoundedBy (I : FixedBox) (q : ℚ) : Bool := decide (q*fixedScale ≤ (I.lo : ℚ))

theorem upperBoundedBy_sound {x : ℝ} {I : FixedBox} {q : ℚ}
    (hx : x ∈ I) (h : I.upperBoundedBy q = true) : x ≤ (q : ℝ) := by
  simp only [upperBoundedBy, decide_eq_true_eq] at h
  have hc : (I.hi : ℝ) ≤ (q : ℝ)*fixedScale := by exact_mod_cast h
  exact le_of_mul_le_mul_right (hx.2.trans hc) fixedScale_real_pos

theorem lowerBoundedBy_sound {x : ℝ} {I : FixedBox} {q : ℚ}
    (hx : x ∈ I) (h : I.lowerBoundedBy q = true) : (q : ℝ) ≤ x := by
  simp only [lowerBoundedBy, decide_eq_true_eq] at h
  have hc : (q : ℝ)*fixedScale ≤ (I.lo : ℝ) := by exact_mod_cast h
  exact le_of_mul_le_mul_right (hc.trans hx.1) fixedScale_real_pos

end FixedBox
end
end ErdosOverlap.Numerics
