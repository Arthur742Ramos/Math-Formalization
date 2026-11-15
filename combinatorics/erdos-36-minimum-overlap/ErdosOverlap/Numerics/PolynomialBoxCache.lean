module

public import ErdosOverlap.Numerics.LeafCache

/-! Source-bound cached coefficient boxes. Arithmetic leaves evaluate only integer
Horner recurrences; the rational coefficient conversions are checked once. -/

namespace ErdosOverlap.Numerics

@[expose] public section

structure PolynomialBoxCache where
  coefficients : List FixedBox
  primitive : List FixedBox
  weightedPrimitive : List FixedBox
  deriving DecidableEq, Repr

def PolynomialBoxCache.check (c : PolynomialBoxCache) (p : PolynomialPiece) : Bool :=
  decide (c.coefficients = p.coefficients.map FixedBox.ofRat ∧
    c.primitive = (primitiveCoeffs p.coefficients).map FixedBox.ofRat ∧
    c.weightedPrimitive = (weightedPrimitiveCoeffs p.coefficients).map FixedBox.ofRat)

def PolynomialBoxCache.rangeBox (c : PolynomialBoxCache) (p : PolynomialPiece)
    (lo hi : ℚ) : FixedBox :=
  FixedBox.hornerBoxes (p.normalizedBox lo hi) c.coefficients

def PolynomialBoxCache.integralBox (c : PolynomialBoxCache) (p : PolynomialPiece)
    (alpha beta lo hi : ℚ) : FixedBox :=
  let u := FixedBox.ofRat ((lo-p.center)/p.radius)
  let v := FixedBox.ofRat ((hi-p.center)/p.radius)
  let first := (FixedBox.hornerBoxes v c.primitive).sub
    (FixedBox.hornerBoxes u c.primitive)
  let second := (FixedBox.hornerBoxes v c.weightedPrimitive).sub
    (FixedBox.hornerBoxes u c.weightedPrimitive)
  (FixedBox.ofRat p.radius).mul
    (((FixedBox.ofRat (alpha+beta*p.center)).mul first).add
      ((FixedBox.ofRat (beta*p.radius)).mul second))

theorem PolynomialBoxCache.rangeBox_eq {c : PolynomialBoxCache} {p : PolynomialPiece}
    (hc : c.check p = true) (lo hi : ℚ) : c.rangeBox p lo hi = p.rangeBox lo hi := by
  simp only [check, decide_eq_true_eq] at hc
  simp only [rangeBox, PolynomialPiece.rangeBox, polynomialBox, hc.1]

theorem PolynomialBoxCache.integralBox_eq {c : PolynomialBoxCache} {p : PolynomialPiece}
    (hc : c.check p = true) (alpha beta lo hi : ℚ) :
    c.integralBox p alpha beta lo hi = p.integralBox alpha beta lo hi := by
  simp only [check, decide_eq_true_eq] at hc
  simp only [integralBox, PolynomialPiece.integralBox, normalizedIntegralBox,
    affineIntegralBox, polynomialBox, hc.2.1, hc.2.2]

def LeafCache.cachedCheck (c : LeafCache) (ca cb : PolynomialBoxCache)
    (PA PB : PolynomialPiece) (lo hi : ℚ) : Bool :=
  (ca.rangeBox PA lo hi).subsetCheck c.rangeA &&
  (cb.rangeBox PB lo hi).subsetCheck c.rangeB &&
  (ca.integralBox PA 1 0 lo hi).subsetCheck c.integrals.integralA &&
  (ca.integralBox PA 0 1 lo hi).subsetCheck c.integrals.momentA &&
  (cb.integralBox PB 1 0 lo hi).subsetCheck c.integrals.integralB &&
  (cb.integralBox PB 0 1 lo hi).subsetCheck c.integrals.momentB

theorem LeafCache.check_of_cachedCheck {c : LeafCache} {ca cb : PolynomialBoxCache}
    {PA PB : PolynomialPiece} {lo hi : ℚ}
    (ha : ca.check PA = true) (hb : cb.check PB = true)
    (h : c.cachedCheck ca cb PA PB lo hi = true) : c.check PA PB lo hi = true := by
  simpa only [cachedCheck, ca.rangeBox_eq ha, cb.rangeBox_eq hb,
    ca.integralBox_eq ha, cb.integralBox_eq hb, check] using h

end
end ErdosOverlap.Numerics
