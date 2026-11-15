module

public import ErdosOverlap.Numerics.Trig

/-! # Outward dyadic Taylor evaluation

The numerical checker evaluates each Taylor polynomial with rounding after
every operation. The following proofs connect that finite computation to the
real Taylor theorem; no floating-point result is trusted.
-/

namespace ErdosOverlap.Numerics

open LeanCert.Core

public section

@[expose] def hornerDyadic (I : IntervalDyadic) (precision : ℤ) :
    List ℚ → IntervalDyadic
  | [] => rationalDyadic 0 precision
  | c :: cs => (rationalDyadic c precision).addRounded
      (I.mulRounded (hornerDyadic I precision cs) precision) precision

theorem mem_hornerDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (precision : ℤ) (hp : precision ≤ 0) (cs : List ℚ) :
    IntervalRat.hornerVal cs x ∈ hornerDyadic I precision cs := by
  induction cs with
  | nil => simpa [IntervalRat.hornerVal, hornerDyadic] using
      mem_rationalDyadic 0 precision hp
  | cons c cs ih =>
    exact IntervalDyadic.roundOut_contains
      (IntervalDyadic.mem_add (mem_rationalDyadic c precision hp)
        (IntervalDyadic.roundOut_contains (IntervalDyadic.mem_mul hx ih) precision)) precision

@[expose] def trigDomain : IntervalRat := ⟨-4, 4, by norm_num⟩

@[expose] def smallCosDyadic (I : IntervalDyadic) (degree : ℕ)
    (precision : ℤ) : IntervalDyadic :=
  (hornerDyadic I precision (IntervalRat.cosTaylorCoeffs degree)).addRounded
    (IntervalDyadic.ofIntervalRat (IntervalRat.cosRemainderBoundComputable trigDomain degree)
      precision) precision

@[expose] def smallSinDyadic (I : IntervalDyadic) (degree : ℕ)
    (precision : ℤ) : IntervalDyadic :=
  (hornerDyadic I precision (IntervalRat.sinTaylorCoeffs degree)).addRounded
    (IntervalDyadic.ofIntervalRat (IntervalRat.sinRemainderBoundComputable trigDomain degree)
      precision) precision

theorem mem_smallCosDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hd : x ∈ trigDomain) (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.cos x ∈ smallCosDyadic I degree precision := by
  have hpoly := mem_hornerDyadic hx precision hp (IntervalRat.cosTaylorCoeffs degree)
  have hrem := IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.cos_taylor_remainder_in_interval hd degree) precision hp
  rw [IntervalRat.taylorSeries_cos_eq_horner] at hrem
  have hadd := IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hpoly hrem) precision
  convert! hadd using 1 <;> simp only [smallCosDyadic, IntervalDyadic.addRounded, add_sub_cancel]

theorem mem_smallSinDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hd : x ∈ trigDomain) (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.sin x ∈ smallSinDyadic I degree precision := by
  have hpoly := mem_hornerDyadic hx precision hp (IntervalRat.sinTaylorCoeffs degree)
  have hrem := IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.sin_taylor_remainder_in_interval hd degree) precision hp
  rw [IntervalRat.taylorSeries_sin_eq_horner] at hrem
  have hadd := IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hpoly hrem) precision
  convert! hadd using 1 <;> simp only [smallSinDyadic, IntervalDyadic.addRounded, add_sub_cancel]

@[expose] def reducedDyadic (I : IntervalDyadic) (precision : ℤ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (TrigReduction.shiftInterval I.toIntervalRat
    (TrigReduction.computeShiftK I.toIntervalRat)) precision

theorem mem_reducedDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (precision : ℤ) (hp : precision ≤ 0) :
    x - 2*Real.pi*(TrigReduction.computeShiftK I.toIntervalRat : ℤ) ∈
      reducedDyadic I precision := by
  exact IntervalDyadic.mem_ofIntervalRat
    (TrigReduction.mem_shiftInterval_of_mem (IntervalDyadic.mem_toIntervalRat.mp hx))
    precision hp

@[expose] def unitDyadic (precision : ℤ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ precision

@[expose] def cosDyadicFast (I : IntervalDyadic) (degree : ℕ)
    (precision : ℤ) : IntervalDyadic :=
  let J := reducedDyadic I precision
  if -4 ≤ J.lo.toRat ∧ J.hi.toRat ≤ 4 then smallCosDyadic J degree precision
  else unitDyadic precision

@[expose] def sinDyadicFast (I : IntervalDyadic) (degree : ℕ)
    (precision : ℤ) : IntervalDyadic :=
  let J := reducedDyadic I precision
  if -4 ≤ J.lo.toRat ∧ J.hi.toRat ≤ 4 then smallSinDyadic J degree precision
  else unitDyadic precision

theorem mem_trigDomain_of_bounds {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (h : -4 ≤ I.lo.toRat ∧ I.hi.toRat ≤ 4) : x ∈ trigDomain := by
  have hx' := IntervalDyadic.mem_toIntervalRat.mp hx
  change ((-4 : ℚ) : ℝ) ≤ x ∧ x ≤ ((4 : ℚ) : ℝ)
  exact ⟨(Rat.cast_le.mpr h.1).trans hx'.1, hx'.2.trans (Rat.cast_le.mpr h.2)⟩

theorem mem_cosDyadicFast {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.cos x ∈ cosDyadicFast I degree precision := by
  have hr := mem_reducedDyadic hx precision hp
  have he : Real.cos x = Real.cos (x-2*Real.pi*(TrigReduction.computeShiftK I.toIntervalRat : ℤ)) := by
    have h := Real.cos_add_int_mul_two_pi x (-(TrigReduction.computeShiftK I.toIntervalRat))
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold cosDyadicFast
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallCosDyadic hr (mem_trigDomain_of_bounds hr hb) degree precision hp
  · apply IntervalDyadic.mem_ofIntervalRat _ precision hp
    change ((-1 : ℚ) : ℝ) ≤ Real.cos x ∧ Real.cos x ≤ ((1 : ℚ) : ℝ)
    norm_num only [Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

theorem mem_sinDyadicFast {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (degree : ℕ) (precision : ℤ) (hp : precision ≤ 0) :
    Real.sin x ∈ sinDyadicFast I degree precision := by
  have hr := mem_reducedDyadic hx precision hp
  have he : Real.sin x = Real.sin (x-2*Real.pi*(TrigReduction.computeShiftK I.toIntervalRat : ℤ)) := by
    have h := Real.sin_add_int_mul_two_pi x (-(TrigReduction.computeShiftK I.toIntervalRat))
    convert h.symm using 1 <;> congr 1 <;> push_cast <;> ring
  unfold sinDyadicFast
  dsimp only []
  split_ifs with hb
  · rw [he]
    exact mem_smallSinDyadic hr (mem_trigDomain_of_bounds hr hb) degree precision hp
  · apply IntervalDyadic.mem_ofIntervalRat _ precision hp
    change ((-1 : ℚ) : ℝ) ≤ Real.sin x ∧ Real.sin x ≤ ((1 : ℚ) : ℝ)
    norm_num only [Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

end
end ErdosOverlap.Numerics
