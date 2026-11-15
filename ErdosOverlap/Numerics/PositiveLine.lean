module

public import ErdosOverlap.Numerics.PolynomialBox

/-! Automatically proved affine majorants of the positive part. -/

namespace ErdosOverlap.Numerics

@[expose] public section

structure RationalAffine where
  constant : ℚ
  slope : ℚ
  deriving DecidableEq, Repr

noncomputable def RationalAffine.value (a : RationalAffine) (x : ℝ) : ℝ :=
  (a.constant : ℝ)+(a.slope : ℝ)*x

def RationalAffine.add (a b : RationalAffine) : RationalAffine :=
  ⟨a.constant+b.constant,a.slope+b.slope⟩

def RationalAffine.sub (a b : RationalAffine) : RationalAffine :=
  ⟨a.constant-b.constant,a.slope-b.slope⟩

def RationalAffine.scale (a : RationalAffine) (q : ℚ) : RationalAffine :=
  ⟨q*a.constant,q*a.slope⟩

def positiveLine (lo hi : ℚ) : RationalAffine :=
  if hi ≤ 0 then ⟨0,0⟩
  else if 0 ≤ lo then ⟨0,1⟩
  else ⟨-lo*hi/(hi-lo),hi/(hi-lo)⟩

theorem positiveLine_sound {lo hi : ℚ} {x : ℝ}
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    max x 0 ≤ (positiveLine lo hi).value x := by
  unfold positiveLine
  split_ifs with hh hl
  · have hh' : (hi : ℝ) ≤ 0 := by exact_mod_cast hh
    simp only [RationalAffine.value, Rat.cast_zero, zero_mul, add_zero]
    exact max_le (hx.2.trans hh') le_rfl
  · have hl' : (0 : ℝ) ≤ lo := by exact_mod_cast hl
    simp only [RationalAffine.value, Rat.cast_zero, Rat.cast_one, one_mul, zero_add]
    exact le_of_eq (max_eq_left (hl'.trans hx.1))
  · have hh' : (0 : ℝ) < hi := by exact_mod_cast lt_of_not_ge hh
    have hl' : (lo : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hl
    have hd : (hi : ℝ)-(lo : ℝ) ≠ 0 := by linarith
    have helo : (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(lo : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) = 0 := by ring
    have hehi : (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(hi : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) = (hi : ℝ) := by
      field_simp
      ring
    have hm := positivePart_le_affine hx
      (show 0 ≤ (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(lo : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) by rw [helo])
      (show (lo : ℝ) ≤ (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(lo : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) by rw [helo]; exact hl'.le)
      (show 0 ≤ (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(hi : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) by rw [hehi]; exact hh'.le)
      (show (hi : ℝ) ≤ (hi : ℝ)/((hi : ℝ)-(lo : ℝ))*(hi : ℝ)+
        (-(lo : ℝ)*(hi : ℝ)/((hi : ℝ)-(lo : ℝ))) by rw [hehi])
    convert! hm using 1 <;> simp only [RationalAffine.value, Rat.cast_div,
      Rat.cast_mul, Rat.cast_neg, Rat.cast_sub] <;> ring

def FixedBox.lowerRat (I : FixedBox) : ℚ := (I.lo : ℚ)/(fixedScale : ℚ)
def FixedBox.upperRat (I : FixedBox) : ℚ := (I.hi : ℚ)/(fixedScale : ℚ)

theorem FixedBox.real_bounds {I : FixedBox} {x : ℝ} (hx : x ∈ I) :
    (I.lowerRat : ℝ) ≤ x ∧ x ≤ (I.upperRat : ℝ) := by
  unfold lowerRat upperRat
  push_cast
  constructor
  · apply (div_le_iff₀ fixedScale_real_pos).mpr
    simpa [mul_comm] using hx.1
  · apply (le_div_iff₀ fixedScale_real_pos).mpr
    simpa [mul_comm] using hx.2

def FixedBox.positiveLine (I : FixedBox) : RationalAffine :=
  Numerics.positiveLine I.lowerRat I.upperRat

theorem FixedBox.positiveLine_sound {I : FixedBox} {x : ℝ} (hx : x ∈ I) :
    max x 0 ≤ I.positiveLine.value x := Numerics.positiveLine_sound (FixedBox.real_bounds hx)

end
end ErdosOverlap.Numerics
