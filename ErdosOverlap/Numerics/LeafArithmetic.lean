module

public import ErdosOverlap.Numerics.PositiveLine
public import ErdosOverlap.Numerics.LeafIntegrationAE

/-! Executable leaf weights and arithmetic, independent of a particular kernel. -/

namespace ErdosOverlap.Numerics

@[expose] public section

def boxSign (I : FixedBox) : ℤ := if 0 ≤ I.lo+I.hi then 1 else -1
def boxPositiveSelector (I : FixedBox) : ℤ := if 0 ≤ I.lo+I.hi then 1 else 0

theorem boxSign_bounds (I : FixedBox) : (-1 : ℝ) ≤ boxSign I ∧ (boxSign I : ℝ) ≤ 1 := by
  unfold boxSign
  split_ifs <;> norm_num

theorem boxPositiveSelector_bounds (I : FixedBox) :
    (0 : ℝ) ≤ boxPositiveSelector I ∧ (boxPositiveSelector I : ℝ) ≤ 1 := by
  unfold boxPositiveSelector
  split_ifs <;> norm_num

def firstGateBox (IA IB : FixedBox) (lam : ℚ) : FixedBox :=
  ((FixedBox.ofRat |lam|).sub (IA.scaleInt (boxSign IA))).add
    (IB.scaleInt (1-boxPositiveSelector IB))

def secondGateBox (IA IB : FixedBox) (lam : ℚ) : FixedBox :=
  ((FixedBox.ofRat |lam|).sub (IA.scaleInt (boxSign IA))).sub
    (IB.scaleInt (boxSign IB))

theorem firstGate_mem {IA IB : FixedBox} {PA PB : ℝ}
    (hA : PA ∈ IA) (hB : PB ∈ IB) (lam : ℚ) :
    |(lam : ℝ)|-(boxSign IA : ℝ)*PA+(1-(boxPositiveSelector IB : ℝ))*PB ∈
      firstGateBox IA IB lam := by
  have h := FixedBox.mem_add
    (FixedBox.mem_sub (FixedBox.mem_ofRat |lam|) (FixedBox.mem_scaleInt hA (boxSign IA)))
    (FixedBox.mem_scaleInt hB (1-boxPositiveSelector IB))
  simpa only [firstGateBox, Rat.cast_abs, Int.cast_sub, Int.cast_one] using h

theorem secondGate_mem {IA IB : FixedBox} {PA PB : ℝ}
    (hA : PA ∈ IA) (hB : PB ∈ IB) (lam : ℚ) :
    |(lam : ℝ)|-(boxSign IA : ℝ)*PA-(boxSign IB : ℝ)*PB ∈
      secondGateBox IA IB lam := by
  simpa only [secondGateBox, Rat.cast_abs] using FixedBox.mem_sub
    (FixedBox.mem_sub (FixedBox.mem_ofRat |lam|) (FixedBox.mem_scaleInt hA (boxSign IA)))
    (FixedBox.mem_scaleInt hB (boxSign IB))

structure LeafWeights where
  weightA : RationalAffine
  weightB : RationalAffine
  weight0 : RationalAffine
  deriving DecidableEq, Repr

noncomputable def LeafWeights.value (w : LeafWeights) (PA PB t : ℝ) : ℝ :=
  w.weightA.value t*PA+w.weightB.value t*PB+w.weight0.value t

def conjugateWeights (IA IB : FixedBox) (lam : ℚ) (L K V : RationalAffine) : LeafWeights :=
  let gate1 := (firstGateBox IA IB lam).positiveLine
  let gate2 := (secondGateBox IA IB lam).positiveLine
  let W := (K.scale gate1.slope).add (V.scale gate2.slope)
  ⟨W.scale (boxSign IA : ℚ),
    ((L.scale (boxPositiveSelector IB : ℚ)).sub
      (K.scale ((1-(boxPositiveSelector IB : ℚ))*gate1.slope))).add
      (V.scale ((boxSign IB : ℚ)*gate2.slope)),
    ((W.scale (-|lam|)).sub (K.scale gate1.constant)).sub (V.scale gate2.constant)⟩

theorem conjugateWeights_value (IA IB : FixedBox) (lam : ℚ) (L K V : RationalAffine)
    (PA PB t : ℝ) :
    (conjugateWeights IA IB lam L K V).value PA PB t =
      expandedMinorant PA PB (L.value t) (K.value t) (V.value t) (lam : ℝ)
        (boxSign IA : ℝ) (boxSign IB : ℝ) (boxPositiveSelector IB : ℝ)
        (1-(boxPositiveSelector IB : ℝ))
        ((firstGateBox IA IB lam).positiveLine.slope : ℝ)
        ((firstGateBox IA IB lam).positiveLine.constant : ℝ)
        ((secondGateBox IA IB lam).positiveLine.slope : ℝ)
        ((secondGateBox IA IB lam).positiveLine.constant : ℝ) := by
  simp only [conjugateWeights, LeafWeights.value, RationalAffine.value,
    RationalAffine.add, RationalAffine.sub, RationalAffine.scale, expandedMinorant]
  push_cast
  ring

theorem conjugateWeights_pointwise {IA IB : FixedBox} {PA PB A B U t delta : ℝ}
    (lam : ℚ) (L K V : RationalAffine)
    (hPA : PA ∈ IA) (hPB : PB ∈ IB)
    (hL : 0 ≤ L.value t ∧ L.value t ≤ 1) (hU : 0 ≤ U ∧ U ≤ 1)
    (hK : K.value t = min U (L.value t)) (hV : V.value t = U-K.value t)
    (hdelta : 0 ≤ delta) (hA : |A-PA| ≤ delta) (hB : |B-PB| ≤ delta) :
    (conjugateWeights IA IB lam L K V).value PA PB t-2*delta ≤
      profileConjugate (max B 0) (|A|+|B|) (L.value t) U (lam : ℝ) := by
  rw [conjugateWeights_value]
  apply actual_conjugate_expanded_minorant hL hU hK hV
    (boxSign_bounds IA) (boxSign_bounds IB) (boxPositiveSelector_bounds IB)
    ⟨by linarith [(boxPositiveSelector_bounds IB).2],
      by linarith [(boxPositiveSelector_bounds IB).1]⟩ _ _ hdelta hA hB
  · simpa only [RationalAffine.value, add_comm] using
      FixedBox.positiveLine_sound (firstGate_mem hPA hPB lam)
  · simpa only [RationalAffine.value, add_comm] using
      FixedBox.positiveLine_sound (secondGate_mem hPA hPB lam)

structure LeafIntegralBoxes where
  integralA : FixedBox
  momentA : FixedBox
  integralB : FixedBox
  momentB : FixedBox
  deriving DecidableEq, Repr

def LeafWeights.integralBox (w : LeafWeights) (I : LeafIntegralBoxes) (lo hi : ℚ) : FixedBox :=
  (((((FixedBox.ofRat w.weightA.constant).mul I.integralA).add
      ((FixedBox.ofRat w.weightA.slope).mul I.momentA)).add
      ((FixedBox.ofRat w.weightB.constant).mul I.integralB)).add
      ((FixedBox.ofRat w.weightB.slope).mul I.momentB)).add
      (((FixedBox.ofRat w.weight0.constant).mul (FixedBox.ofRat (hi-lo))).add
       ((FixedBox.ofRat w.weight0.slope).mul (FixedBox.ofRat ((hi^2-lo^2)/2))))

theorem LeafWeights.integral_mem_box (w : LeafWeights) (I : LeafIntegralBoxes)
    (lo hi : ℚ) {a ax b bx : ℝ}
    (ha : a ∈ I.integralA) (hax : ax ∈ I.momentA)
    (hb : b ∈ I.integralB) (hbx : bx ∈ I.momentB) :
    (w.weightA.constant : ℝ)*a+(w.weightA.slope : ℝ)*ax+
      (w.weightB.constant : ℝ)*b+(w.weightB.slope : ℝ)*bx+
      (w.weight0.constant : ℝ)*((hi : ℝ)-(lo : ℝ))+
      (w.weight0.slope : ℝ)*(((hi : ℝ)^2-(lo : ℝ)^2)/2) ∈
      w.integralBox I lo hi := by
  have h := FixedBox.mem_add
    (FixedBox.mem_add (FixedBox.mem_add
      (FixedBox.mem_add (FixedBox.mem_mul (FixedBox.mem_ofRat w.weightA.constant) ha)
        (FixedBox.mem_mul (FixedBox.mem_ofRat w.weightA.slope) hax))
      (FixedBox.mem_mul (FixedBox.mem_ofRat w.weightB.constant) hb))
      (FixedBox.mem_mul (FixedBox.mem_ofRat w.weightB.slope) hbx))
    (FixedBox.mem_add
      (FixedBox.mem_mul (FixedBox.mem_ofRat w.weight0.constant) (FixedBox.mem_ofRat (hi-lo)))
      (FixedBox.mem_mul (FixedBox.mem_ofRat w.weight0.slope) (FixedBox.mem_ofRat ((hi^2-lo^2)/2))))
  convert! h using 1 <;> push_cast <;> ring

end
end ErdosOverlap.Numerics
