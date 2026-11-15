module

public import ErdosOverlap.Numerics.LeafArithmetic
public import ErdosOverlap.Numerics.NativePolynomialPatch

/-! Reusable polynomial range and integral certificates for a geometric leaf. -/

namespace ErdosOverlap.Numerics

open MeasureTheory Set

@[expose] public section

def FixedBox.subsetCheck (I J : FixedBox) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

theorem FixedBox.mem_of_subsetCheck {I J : FixedBox} {x : ℝ}
    (hx : x ∈ I) (h : I.subsetCheck J = true) : x ∈ J := by
  simp only [subsetCheck, decide_eq_true_eq] at h
  exact ⟨(by exact_mod_cast h.1 : (J.lo : ℝ) ≤ I.lo).trans hx.1,
    hx.2.trans (by exact_mod_cast h.2 : (I.hi : ℝ) ≤ J.hi)⟩

structure LeafCache where
  rangeA : FixedBox
  rangeB : FixedBox
  integrals : LeafIntegralBoxes
  deriving DecidableEq, Repr

def LeafCache.check (c : LeafCache) (PA PB : PolynomialPiece) (lo hi : ℚ) : Bool :=
  (PA.rangeBox lo hi).subsetCheck c.rangeA &&
  (PB.rangeBox lo hi).subsetCheck c.rangeB &&
  (PA.integralBox 1 0 lo hi).subsetCheck c.integrals.integralA &&
  (PA.integralBox 0 1 lo hi).subsetCheck c.integrals.momentA &&
  (PB.integralBox 1 0 lo hi).subsetCheck c.integrals.integralB &&
  (PB.integralBox 0 1 lo hi).subsetCheck c.integrals.momentB

noncomputable def LeafCache.Correct (c : LeafCache) (PA PB : PolynomialPiece)
    (lo hi : ℚ) : Prop :=
  (∀ t ∈ Icc (lo : ℝ) (hi : ℝ), PA.value t ∈ c.rangeA ∧ PB.value t ∈ c.rangeB) ∧
  (∫ t in (lo : ℝ)..(hi : ℝ), PA.value t) ∈ c.integrals.integralA ∧
  (∫ t in (lo : ℝ)..(hi : ℝ), t*PA.value t) ∈ c.integrals.momentA ∧
  (∫ t in (lo : ℝ)..(hi : ℝ), PB.value t) ∈ c.integrals.integralB ∧
  (∫ t in (lo : ℝ)..(hi : ℝ), t*PB.value t) ∈ c.integrals.momentB

theorem LeafCache.check_sound {c : LeafCache} {PA PB : PolynomialPiece} {lo hi : ℚ}
    (hA : PA.radius ≠ 0) (hB : PB.radius ≠ 0)
    (h : c.check PA PB lo hi = true) : c.Correct PA PB lo hi := by
  simp only [check, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hrA,hrB⟩,hiA⟩,hmA⟩,hiB⟩,hmB⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨FixedBox.mem_of_subsetCheck (PA.value_mem_rangeBox ht) hrA,
      FixedBox.mem_of_subsetCheck (PB.value_mem_rangeBox ht) hrB⟩
  · have ha := PA.integral_mem_box 1 0 lo hi hA
    have hb := FixedBox.mem_of_subsetCheck ha hiA
    simpa using hb
  · have ha := PA.integral_mem_box 0 1 lo hi hA
    have hb := FixedBox.mem_of_subsetCheck ha hmA
    simpa using hb
  · have ha := PB.integral_mem_box 1 0 lo hi hB
    have hb := FixedBox.mem_of_subsetCheck ha hiB
    simpa using hb
  · have ha := PB.integral_mem_box 0 1 lo hi hB
    have hb := FixedBox.mem_of_subsetCheck ha hmB
    simpa using hb

theorem LeafWeights.integral_value (w : LeafWeights) (PA PB : PolynomialPiece) (lo hi : ℝ) :
    (∫ t in lo..hi, w.value (PA.value t) (PB.value t) t) =
      (w.weightA.constant : ℝ)*(∫ t in lo..hi, PA.value t)+
      (w.weightA.slope : ℝ)*(∫ t in lo..hi, t*PA.value t)+
      (w.weightB.constant : ℝ)*(∫ t in lo..hi, PB.value t)+
      (w.weightB.slope : ℝ)*(∫ t in lo..hi, t*PB.value t)+
      (w.weight0.constant : ℝ)*(hi-lo)+
      (w.weight0.slope : ℝ)*((hi^2-lo^2)/2) := by
  have hpa := PA.continuous.intervalIntegrable (μ := volume) lo hi
  have hpb := PB.continuous.intervalIntegrable (μ := volume) lo hi
  have hxa : IntervalIntegrable (fun t : ℝ => t*PA.value t) volume lo hi := by
    convert! (continuous_id.mul PA.continuous).intervalIntegrable (μ := volume) lo hi using 1
  have hxb : IntervalIntegrable (fun t : ℝ => t*PB.value t) volume lo hi := by
    convert! (continuous_id.mul PB.continuous).intervalIntegrable (μ := volume) lo hi using 1
  have hc : IntervalIntegrable (fun _ : ℝ => (w.weight0.constant : ℝ)) volume lo hi := intervalIntegrable_const
  have hx : IntervalIntegrable (fun t : ℝ => (w.weight0.slope : ℝ)*t) volume lo hi := by
    convert! (continuous_id.const_mul (w.weight0.slope : ℝ)).intervalIntegrable
      (μ := volume) lo hi using 1
  have hlin : (∫ t in lo..hi, (w.weight0.slope : ℝ)*t) =
      (w.weight0.slope : ℝ)*((hi^2-lo^2)/2) := by
    calc
      _ = (w.weight0.slope : ℝ)*(∫ t in lo..hi, t) := by
        convert! intervalIntegral.integral_const_mul (μ := volume) (a := lo) (b := hi)
          (w.weight0.slope : ℝ) (fun t : ℝ => t) using 1
      _ = _ := by rw [integral_id]
  calc
    _ = ∫ t in lo..hi, (w.weightA.constant : ℝ)*PA.value t+
        (w.weightA.slope : ℝ)*(t*PA.value t)+
        (w.weightB.constant : ℝ)*PB.value t+
        (w.weightB.slope : ℝ)*(t*PB.value t)+
        (w.weight0.constant : ℝ)+(w.weight0.slope : ℝ)*t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [LeafWeights.value, RationalAffine.value]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (((((hpa.const_mul _).add (hxa.const_mul _)).add (hpb.const_mul _)).add
          (hxb.const_mul _)).add hc) hx]
      rw [intervalIntegral.integral_add
        ((((hpa.const_mul _).add (hxa.const_mul _)).add (hpb.const_mul _)).add
          (hxb.const_mul _)) hc]
      rw [intervalIntegral.integral_add
        (((hpa.const_mul _).add (hxa.const_mul _)).add (hpb.const_mul _)) (hxb.const_mul _)]
      rw [intervalIntegral.integral_add ((hpa.const_mul _).add (hxa.const_mul _)) (hpb.const_mul _)]
      rw [intervalIntegral.integral_add (hpa.const_mul _) (hxa.const_mul _)]
      rw [hlin]
      simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        smul_eq_mul, integral_id]
      ring

theorem LeafCache.weights_integral_mem {c : LeafCache} {PA PB : PolynomialPiece} {lo hi : ℚ}
    (h : c.Correct PA PB lo hi) (w : LeafWeights) :
    (∫ t in (lo : ℝ)..(hi : ℝ), w.value (PA.value t) (PB.value t) t) ∈
      w.integralBox c.integrals lo hi := by
  rw [w.integral_value]
  exact w.integral_mem_box c.integrals lo hi h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

end
end ErdosOverlap.Numerics
