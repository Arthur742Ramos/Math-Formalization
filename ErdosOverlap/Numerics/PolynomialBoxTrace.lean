module

public import ErdosOverlap.Numerics.PolynomialBoxCache
public import ErdosOverlap.Numerics.HornerCheckpoint

/-! Literal checkpoints keep exact interval polynomial evaluation bounded in
depth. Every checkpoint is verified by the Lean kernel; the resulting boxes
are proved equal to the original unaccelerated computation. -/

namespace ErdosOverlap.Numerics

@[expose] public section

structure HornerTrace where
  result : FixedBox
  tails : List FixedBox
  deriving DecidableEq, Repr

def HornerTrace.check (t : HornerTrace) (I : FixedBox) (cs : List FixedBox) : Bool :=
  FixedBox.hornerCheckpointCheck I 5 cs t.result t.tails

theorem HornerTrace.result_eq {t : HornerTrace} {I : FixedBox} {cs : List FixedBox}
    (h : t.check I cs = true) : t.result = FixedBox.hornerBoxes I cs :=
  FixedBox.hornerCheckpointCheck_sound h

structure PolynomialBoxTrace where
  range : HornerTrace
  primitiveLo : HornerTrace
  primitiveHi : HornerTrace
  weightedLo : HornerTrace
  weightedHi : HornerTrace
  deriving DecidableEq, Repr

def PolynomialBoxTrace.check (t : PolynomialBoxTrace) (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.range.check (p.normalizedBox lo hi) c.coefficients &&
  t.primitiveLo.check (FixedBox.ofRat ((lo-p.center)/p.radius)) c.primitive &&
  t.primitiveHi.check (FixedBox.ofRat ((hi-p.center)/p.radius)) c.primitive &&
  t.weightedLo.check (FixedBox.ofRat ((lo-p.center)/p.radius)) c.weightedPrimitive &&
  t.weightedHi.check (FixedBox.ofRat ((hi-p.center)/p.radius)) c.weightedPrimitive

def PolynomialBoxTrace.integralBox (t : PolynomialBoxTrace) (p : PolynomialPiece)
    (alpha beta : ℚ) : FixedBox :=
  let first := t.primitiveHi.result.sub t.primitiveLo.result
  let second := t.weightedHi.result.sub t.weightedLo.result
  (FixedBox.ofRat p.radius).mul
    (((FixedBox.ofRat (alpha+beta*p.center)).mul first).add
      ((FixedBox.ofRat (beta*p.radius)).mul second))

theorem PolynomialBoxTrace.range_eq {t : PolynomialBoxTrace} {c : PolynomialBoxCache}
    {p : PolynomialPiece} {lo hi : ℚ} (h : t.check c p lo hi = true) :
    t.range.result = c.rangeBox p lo hi := by
  simp only [check, Bool.and_eq_true] at h
  exact HornerTrace.result_eq h.1.1.1.1

theorem PolynomialBoxTrace.integralBox_eq {t : PolynomialBoxTrace} {c : PolynomialBoxCache}
    {p : PolynomialPiece} {lo hi : ℚ} (h : t.check c p lo hi = true) (alpha beta : ℚ) :
    t.integralBox p alpha beta = c.integralBox p alpha beta lo hi := by
  simp only [check, Bool.and_eq_true] at h
  simp only [integralBox, PolynomialBoxCache.integralBox,
    HornerTrace.result_eq h.1.1.1.2, HornerTrace.result_eq h.1.1.2,
    HornerTrace.result_eq h.1.2, HornerTrace.result_eq h.2]

def LeafCache.tracedCheck (c : LeafCache) (ta tb : PolynomialBoxTrace)
    (PA PB : PolynomialPiece) : Bool :=
  ta.range.result.subsetCheck c.rangeA &&
  tb.range.result.subsetCheck c.rangeB &&
  (ta.integralBox PA 1 0).subsetCheck c.integrals.integralA &&
  (ta.integralBox PA 0 1).subsetCheck c.integrals.momentA &&
  (tb.integralBox PB 1 0).subsetCheck c.integrals.integralB &&
  (tb.integralBox PB 0 1).subsetCheck c.integrals.momentB

theorem LeafCache.cachedCheck_of_tracedCheck {c : LeafCache} {ca cb : PolynomialBoxCache}
    {ta tb : PolynomialBoxTrace} {PA PB : PolynomialPiece} {lo hi : ℚ}
    (ha : ta.check ca PA lo hi = true) (hb : tb.check cb PB lo hi = true)
    (h : c.tracedCheck ta tb PA PB = true) : c.cachedCheck ca cb PA PB lo hi = true := by
  simpa only [tracedCheck, ta.range_eq ha, tb.range_eq hb,
    ta.integralBox_eq ha, tb.integralBox_eq hb, cachedCheck] using h

end
end ErdosOverlap.Numerics
