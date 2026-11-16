/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.PolynomialBoxTrace

/-!
# Division-free verification of exact fixed-point Horner steps

The checker verifies a proposed quotient by integer inequalities. It never
evaluates division. The soundness theorem recovers exactly the original
floor and ceiling, so the checked trace has identical arithmetic semantics.
-/

@[expose] public section

namespace ErdosOverlap.Numerics

def signedFloorCheck (n q : ℤ) : Bool :=
  decide (q*fixedScale ≤ n ∧ n < (q+1)*fixedScale)

theorem signedFloorCheck_sound {n q : ℤ} (hc : signedFloorCheck n q = true) :
    n/fixedScale = q := by
  have h : q*fixedScale ≤ n ∧ n < (q+1)*fixedScale := of_decide_eq_true hc
  apply (Int.ediv_eq_iff_of_pos fixedScale_pos).mpr
  exact ⟨h.1, by simpa only [add_mul, one_mul] using h.2⟩

def signedCeilCheck (n q : ℤ) : Bool :=
  decide ((q-1)*fixedScale < n ∧ n ≤ q*fixedScale)

theorem signedCeilCheck_sound {n q : ℤ} (hc : signedCeilCheck n q = true) :
    -((-n)/fixedScale) = q := by
  have h : (q-1)*fixedScale < n ∧ n ≤ q*fixedScale := of_decide_eq_true hc
  have hn : (-n)/fixedScale = -q := by
    apply (Int.ediv_eq_iff_of_pos fixedScale_pos).mpr
    constructor <;> nlinarith [h.1, h.2]
  rw [hn, neg_neg]

namespace FixedBox

def hornerStepCheck (I c next result : FixedBox) : Bool :=
  signedFloorCheck (I.minProduct next) (result.lo-c.lo) &&
    signedCeilCheck (I.maxProduct next) (result.hi-c.hi)

theorem hornerStepCheck_sound {I c next result : FixedBox}
    (hc : hornerStepCheck I c next result = true) :
    result = c.add (I.mul next) := by
  have hs := Bool.and_eq_true_iff.mp hc
  have hlo := signedFloorCheck_sound hs.1
  have hhi := signedCeilCheck_sound hs.2
  cases result with
  | mk lo hi =>
    dsimp only at hlo hhi
    simp only [add, mul, hlo, hhi, add_sub_cancel]

def hornerExactCheck (I : FixedBox) : List FixedBox → FixedBox → List FixedBox → Bool
  | [], result, [] => decide (result = ⟨0,0⟩)
  | c :: cs, result, next :: rest =>
    hornerStepCheck I c next result && hornerExactCheck I cs next rest
  | _, _, _ => false

theorem hornerExactCheck_sound {I : FixedBox} {cs : List FixedBox}
    {result : FixedBox} {tails : List FixedBox}
    (hc : hornerExactCheck I cs result tails = true) :
    result = hornerBoxes I cs := by
  induction cs generalizing result tails with
  | nil =>
    cases tails with
    | nil =>
      have h : result = ⟨0,0⟩ := of_decide_eq_true hc
      rw [h]
      norm_num [hornerBoxes, ofRat]
      decide +kernel
    | cons next rest => simp only [hornerExactCheck, Bool.false_eq_true] at hc
  | cons c cs ih =>
    cases tails with
    | nil => simp only [hornerExactCheck, Bool.false_eq_true] at hc
    | cons next rest =>
      have hs := Bool.and_eq_true_iff.mp hc
      rw [hornerStepCheck_sound hs.1, ih hs.2]
      rfl

end FixedBox

def HornerTrace.checkExact (t : HornerTrace) (I : FixedBox) (cs : List FixedBox) : Bool :=
  FixedBox.hornerExactCheck I cs t.result t.tails

theorem HornerTrace.result_eq_of_exact {t : HornerTrace} {I : FixedBox} {cs : List FixedBox}
    (hc : t.checkExact I cs = true) : t.result = FixedBox.hornerBoxes I cs :=
  FixedBox.hornerExactCheck_sound hc

def PolynomialBoxTrace.checkExact (t : PolynomialBoxTrace) (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.range.checkExact (p.normalizedBox lo hi) c.coefficients &&
  t.primitiveLo.checkExact (FixedBox.ofRat ((lo-p.center)/p.radius)) c.primitive &&
  t.primitiveHi.checkExact (FixedBox.ofRat ((hi-p.center)/p.radius)) c.primitive &&
  t.weightedLo.checkExact (FixedBox.ofRat ((lo-p.center)/p.radius)) c.weightedPrimitive &&
  t.weightedHi.checkExact (FixedBox.ofRat ((hi-p.center)/p.radius)) c.weightedPrimitive

theorem PolynomialBoxTrace.range_eq_of_exact {t : PolynomialBoxTrace} {c : PolynomialBoxCache}
    {p : PolynomialPiece} {lo hi : ℚ} (h : t.checkExact c p lo hi = true) :
    t.range.result = c.rangeBox p lo hi := by
  simp only [checkExact, Bool.and_eq_true] at h
  exact HornerTrace.result_eq_of_exact h.1.1.1.1

theorem PolynomialBoxTrace.integralBox_eq_of_exact
    {t : PolynomialBoxTrace} {c : PolynomialBoxCache}
    {p : PolynomialPiece} {lo hi : ℚ} (h : t.checkExact c p lo hi = true) (alpha beta : ℚ) :
    t.integralBox p alpha beta = c.integralBox p alpha beta lo hi := by
  simp only [checkExact, Bool.and_eq_true] at h
  simp only [integralBox, PolynomialBoxCache.integralBox,
    HornerTrace.result_eq_of_exact h.1.1.1.2, HornerTrace.result_eq_of_exact h.1.1.2,
    HornerTrace.result_eq_of_exact h.1.2, HornerTrace.result_eq_of_exact h.2]

theorem LeafCache.cachedCheck_of_exactTrace {c : LeafCache} {ca cb : PolynomialBoxCache}
    {ta tb : PolynomialBoxTrace} {PA PB : PolynomialPiece} {lo hi : ℚ}
    (ha : ta.checkExact ca PA lo hi = true) (hb : tb.checkExact cb PB lo hi = true)
    (h : c.tracedCheck ta tb PA PB = true) : c.cachedCheck ca cb PA PB lo hi = true := by
  simpa only [tracedCheck, ta.range_eq_of_exact ha, tb.range_eq_of_exact hb,
    ta.integralBox_eq_of_exact ha, tb.integralBox_eq_of_exact hb, cachedCheck] using h

end ErdosOverlap.Numerics
