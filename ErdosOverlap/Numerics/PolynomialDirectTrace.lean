module

public import ErdosOverlap.Numerics.PolynomialInputCache

/-! Direct source-bound endpoint evaluations, sharing every polynomial value
before any integral or moment formula consumes it. -/

namespace ErdosOverlap.Numerics

@[expose] public section

def CachedPolynomialTrace.directCheck (t : CachedPolynomialTrace) (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi && decide (
    t.trace.range.result = FixedBox.hornerBoxes t.inputs.range c.coefficients ∧
    t.trace.primitiveLo.result = FixedBox.hornerBoxes t.inputs.lo c.primitive ∧
    t.trace.primitiveHi.result = FixedBox.hornerBoxes t.inputs.hi c.primitive ∧
    t.trace.weightedLo.result = FixedBox.hornerBoxes t.inputs.lo c.weightedPrimitive ∧
    t.trace.weightedHi.result = FixedBox.hornerBoxes t.inputs.hi c.weightedPrimitive)

theorem CachedPolynomialTrace.range_eq_of_direct {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (h : t.directCheck c p lo hi = true) : t.trace.range.result = c.rangeBox p lo hi := by
  simp only [directCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hI := of_decide_eq_true h.1
  change t.inputs.range = p.normalizedBox lo hi ∧ _ at hI
  simpa only [PolynomialBoxCache.rangeBox, hI.1] using h.2.1

theorem CachedPolynomialTrace.integralBox_eq_of_direct {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (h : t.directCheck c p lo hi = true) (alpha beta : ℚ) :
    t.trace.integralBox p alpha beta = c.integralBox p alpha beta lo hi := by
  simp only [directCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hI := of_decide_eq_true h.1
  change t.inputs.range = p.normalizedBox lo hi ∧
    t.inputs.lo = FixedBox.ofRat ((lo-p.center)/p.radius) ∧
    t.inputs.hi = FixedBox.ofRat ((hi-p.center)/p.radius) at hI
  simp only [PolynomialBoxTrace.integralBox, PolynomialBoxCache.integralBox,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hI.2.1, hI.2.2]

theorem LeafCache.cachedCheck_of_directTrace {c : LeafCache} {ca cb : PolynomialBoxCache}
    {ta tb : CachedPolynomialTrace} {PA PB : PolynomialPiece} {lo hi : ℚ}
    (ha : ta.directCheck ca PA lo hi = true) (hb : tb.directCheck cb PB lo hi = true)
    (h : c.tracedCheck ta.trace tb.trace PA PB = true) :
    c.cachedCheck ca cb PA PB lo hi = true := by
  simpa only [tracedCheck, ta.range_eq_of_direct ha, tb.range_eq_of_direct hb,
    ta.integralBox_eq_of_direct ha, tb.integralBox_eq_of_direct hb, cachedCheck] using h

end
end ErdosOverlap.Numerics
