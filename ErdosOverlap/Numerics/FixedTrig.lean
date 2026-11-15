module

public import ErdosOverlap.Numerics.FixedBox
public import LeanCert.Core.TrigReduction

/-! # Kernel-checkable trigonometry with compact integer intervals -/

namespace ErdosOverlap.Numerics

open LeanCert.Core

@[expose] public section

namespace FixedBox

def horner (I : FixedBox) : List ℚ → FixedBox
  | [] => ofRat 0
  | c :: cs => (ofRat c).add (I.mul (horner I cs))

theorem mem_horner {x : ℝ} {I : FixedBox} (hx : x ∈ I) (cs : List ℚ) :
    IntervalRat.hornerVal cs x ∈ I.horner cs := by
  induction cs with
  | nil => simpa [IntervalRat.hornerVal, horner] using mem_ofRat 0
  | cons c cs ih => exact mem_add (mem_ofRat c) (mem_mul hx ih)

def trigDomain : IntervalRat := ⟨-4, 4, by norm_num⟩

def smallCos (I : FixedBox) (degree : ℕ) : FixedBox :=
  (I.horner (IntervalRat.cosTaylorCoeffs degree)).add
    (ofIntervalRat (IntervalRat.cosRemainderBoundComputable trigDomain degree))

def smallSin (I : FixedBox) (degree : ℕ) : FixedBox :=
  (I.horner (IntervalRat.sinTaylorCoeffs degree)).add
    (ofIntervalRat (IntervalRat.sinRemainderBoundComputable trigDomain degree))

theorem mem_smallCos {x : ℝ} {I : FixedBox} (hx : x ∈ I)
    (hd : x ∈ trigDomain) (degree : ℕ) : Real.cos x ∈ I.smallCos degree := by
  have hpoly := mem_horner hx (IntervalRat.cosTaylorCoeffs degree)
  have hrem := mem_ofIntervalRat (IntervalRat.cos_taylor_remainder_in_interval hd degree)
  rw [IntervalRat.taylorSeries_cos_eq_horner] at hrem
  have hadd := mem_add hpoly hrem
  convert! hadd using 1
  ring

theorem mem_smallSin {x : ℝ} {I : FixedBox} (hx : x ∈ I)
    (hd : x ∈ trigDomain) (degree : ℕ) : Real.sin x ∈ I.smallSin degree := by
  have hpoly := mem_horner hx (IntervalRat.sinTaylorCoeffs degree)
  have hrem := mem_ofIntervalRat (IntervalRat.sin_taylor_remainder_in_interval hd degree)
  rw [IntervalRat.taylorSeries_sin_eq_horner] at hrem
  have hadd := mem_add hpoly hrem
  convert! hadd using 1
  ring

def piBox : FixedBox := ⟨1069028584064966747858780876442842309226, 1069028584064966747862183700112051693862⟩

theorem piBox_exact :
    piBox = ⟨(ofRat TrigReduction.piRatLo).lo, (ofRat TrigReduction.piRatHi).hi⟩ := by
  decide +kernel

theorem pi_mem_piBox : Real.pi ∈ piBox := by
  rw [piBox_exact]
  have hl := (mem_ofRat TrigReduction.piRatLo).1
  have hh := (mem_ofRat TrigReduction.piRatHi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_right TrigReduction.piRatLo_lt_pi.le fixedScale_real_pos.le),
    (mul_le_mul_of_nonneg_right TrigReduction.pi_lt_piRatHi.le fixedScale_real_pos.le).trans hh⟩

/-- Only efficiency depends on this choice; the proof permits any integer shift. -/
def shiftIndex (I : FixedBox) : ℤ := (I.lo+I.hi+2*piBox.lo)/(4*piBox.lo)

def reduced (I : FixedBox) : FixedBox := I.sub (piBox.scaleInt (2*I.shiftIndex))

theorem mem_reduced {x : ℝ} {I : FixedBox} (hx : x ∈ I) :
    x-2*Real.pi*(I.shiftIndex : ℝ) ∈ I.reduced := by
  have h := mem_sub hx (mem_scaleInt pi_mem_piBox (2*I.shiftIndex))
  convert! h using 1
  push_cast
  ring

def unit : FixedBox := ⟨-fixedScale, fixedScale⟩

theorem mem_unit {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) : x ∈ unit := by
  change ((-fixedScale : ℤ) : ℝ) ≤ x*fixedScale ∧ x*fixedScale ≤ (fixedScale : ℝ)
  push_cast
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hx.1 fixedScale_real_pos.le]
  · nlinarith [mul_le_mul_of_nonneg_right hx.2 fixedScale_real_pos.le]

def cos (I : FixedBox) (degree : ℕ) : FixedBox :=
  let J := I.reduced
  if -4*fixedScale ≤ J.lo ∧ J.hi ≤ 4*fixedScale then J.smallCos degree else unit

def sin (I : FixedBox) (degree : ℕ) : FixedBox :=
  let J := I.reduced
  if -4*fixedScale ≤ J.lo ∧ J.hi ≤ 4*fixedScale then J.smallSin degree else unit

theorem mem_trigDomain_of_bounds {x : ℝ} {I : FixedBox} (hx : x ∈ I)
    (h : -4*fixedScale ≤ I.lo ∧ I.hi ≤ 4*fixedScale) : x ∈ trigDomain := by
  have hl : (-4 : ℝ)*fixedScale ≤ (I.lo : ℝ) := by exact_mod_cast h.1
  have hh : (I.hi : ℝ) ≤ (4 : ℝ)*fixedScale := by exact_mod_cast h.2
  change ((-4 : ℚ) : ℝ) ≤ x ∧ x ≤ ((4 : ℚ) : ℝ)
  norm_num only [Rat.cast_neg, Rat.cast_ofNat]
  exact ⟨le_of_mul_le_mul_right (hl.trans hx.1) fixedScale_real_pos,
    le_of_mul_le_mul_right (hx.2.trans hh) fixedScale_real_pos⟩

theorem mem_cos {x : ℝ} {I : FixedBox} (hx : x ∈ I) (degree : ℕ) :
    Real.cos x ∈ I.cos degree := by
  have hr := mem_reduced hx
  have he : Real.cos x = Real.cos (x-2*Real.pi*(I.shiftIndex : ℝ)) := by
    have h := Real.cos_add_int_mul_two_pi x (-I.shiftIndex)
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold cos
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallCos hr (mem_trigDomain_of_bounds hr hb) degree
  · exact mem_unit ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

theorem mem_sin {x : ℝ} {I : FixedBox} (hx : x ∈ I) (degree : ℕ) :
    Real.sin x ∈ I.sin degree := by
  have hr := mem_reduced hx
  have he : Real.sin x = Real.sin (x-2*Real.pi*(I.shiftIndex : ℝ)) := by
    have h := Real.sin_add_int_mul_two_pi x (-I.shiftIndex)
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold sin
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallSin hr (mem_trigDomain_of_bounds hr hb) degree
  · exact mem_unit ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

end FixedBox
end
end ErdosOverlap.Numerics
