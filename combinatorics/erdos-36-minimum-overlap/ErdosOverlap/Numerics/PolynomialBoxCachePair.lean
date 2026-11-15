/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.PolynomialBoxCache

/-!
# Shared primitive evaluations for an integral and its first moment

The two component boxes are exactly the original cached boxes. Keeping the
unit and zero multipliers in the first component makes that identity valid
for arbitrary box data, without adding a validity premise to the checker.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def PolynomialBoxCache.primitiveDifferences (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : FixedBox × FixedBox :=
  let u := FixedBox.ofRat ((lo - p.center) / p.radius)
  let v := FixedBox.ofRat ((hi - p.center) / p.radius)
  ⟨(FixedBox.hornerBoxes v c.primitive).sub (FixedBox.hornerBoxes u c.primitive),
    (FixedBox.hornerBoxes v c.weightedPrimitive).sub
      (FixedBox.hornerBoxes u c.weightedPrimitive)⟩

@[expose] def PolynomialBoxCache.integralPair (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : FixedBox × FixedBox :=
  let d := c.primitiveDifferences p lo hi
  let radius := FixedBox.ofRat p.radius
  ⟨radius.mul (((FixedBox.ofRat 1).mul d.1).add ((FixedBox.ofRat 0).mul d.2)),
    radius.mul (((FixedBox.ofRat p.center).mul d.1).add (radius.mul d.2))⟩

theorem PolynomialBoxCache.integralPair_fst_eq (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) :
    (c.integralPair p lo hi).1 = c.integralBox p 1 0 lo hi := by
  simp only [integralPair, primitiveDifferences, integralBox, zero_mul, add_zero]

theorem PolynomialBoxCache.integralPair_snd_eq (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) :
    (c.integralPair p lo hi).2 = c.integralBox p 0 1 lo hi := by
  simp only [integralPair, primitiveDifferences, integralBox, one_mul, zero_add]

@[expose] def LeafCache.cachedPairCheck (c : LeafCache) (ca cb : PolynomialBoxCache)
    (PA PB : PolynomialPiece) (lo hi : ℚ) : Bool :=
  let ia := ca.integralPair PA lo hi
  let ib := cb.integralPair PB lo hi
  (ca.rangeBox PA lo hi).subsetCheck c.rangeA &&
  (cb.rangeBox PB lo hi).subsetCheck c.rangeB &&
  ia.1.subsetCheck c.integrals.integralA &&
  ia.2.subsetCheck c.integrals.momentA &&
  ib.1.subsetCheck c.integrals.integralB &&
  ib.2.subsetCheck c.integrals.momentB

theorem LeafCache.cachedCheck_of_pair {c : LeafCache} {ca cb : PolynomialBoxCache}
    {PA PB : PolynomialPiece} {lo hi : ℚ}
    (h : c.cachedPairCheck ca cb PA PB lo hi = true) :
    c.cachedCheck ca cb PA PB lo hi = true := by
  simpa only [cachedPairCheck, PolynomialBoxCache.integralPair_fst_eq,
    PolynomialBoxCache.integralPair_snd_eq, cachedCheck] using h

theorem LeafCache.check_of_cachedPairCheck {c : LeafCache} {ca cb : PolynomialBoxCache}
    {PA PB : PolynomialPiece} {lo hi : ℚ}
    (ha : ca.check PA = true) (hb : cb.check PB = true)
    (h : c.cachedPairCheck ca cb PA PB lo hi = true) : c.check PA PB lo hi = true :=
  check_of_cachedCheck ha hb (cachedCheck_of_pair h)

end
end ErdosOverlap.Numerics
