module

public import ErdosOverlap.Numerics.HornerExactStep

/-! Exact normalized-coordinate caches. Each rational conversion is checked
once, before the integer-only Horner trace consumes its literal result. -/

namespace ErdosOverlap.Numerics

@[expose] public section

structure PolynomialInputCache where
  range : FixedBox
  lo : FixedBox
  hi : FixedBox
  deriving DecidableEq, Repr

def PolynomialInputCache.check (c : PolynomialInputCache) (p : PolynomialPiece)
    (lo hi : ℚ) : Bool :=
  decide (c.range = p.normalizedBox lo hi ∧
    c.lo = FixedBox.ofRat ((lo-p.center)/p.radius) ∧
    c.hi = FixedBox.ofRat ((hi-p.center)/p.radius))

def PolynomialBoxTrace.inputCheck (t : PolynomialBoxTrace) (I : PolynomialInputCache)
    (c : PolynomialBoxCache) : Bool :=
  t.range.checkExact I.range c.coefficients &&
  t.primitiveLo.checkExact I.lo c.primitive &&
  t.primitiveHi.checkExact I.hi c.primitive &&
  t.weightedLo.checkExact I.lo c.weightedPrimitive &&
  t.weightedHi.checkExact I.hi c.weightedPrimitive

theorem PolynomialBoxTrace.inputCheck_eq {t : PolynomialBoxTrace}
    {I : PolynomialInputCache} {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (h : I.check p lo hi = true) : t.inputCheck I c = t.checkExact c p lo hi := by
  simp only [PolynomialInputCache.check, decide_eq_true_eq] at h
  simp only [inputCheck, checkExact, h.1, h.2.1, h.2.2]

structure CachedPolynomialTrace where
  inputs : PolynomialInputCache
  trace : PolynomialBoxTrace
  deriving DecidableEq, Repr

def CachedPolynomialTrace.check (t : CachedPolynomialTrace) (c : PolynomialBoxCache)
    (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi && t.trace.inputCheck t.inputs c

theorem CachedPolynomialTrace.check_sound {t : CachedPolynomialTrace}
    {c : PolynomialBoxCache} {p : PolynomialPiece} {lo hi : ℚ}
    (h : t.check c p lo hi = true) : t.trace.checkExact c p lo hi = true := by
  simp only [check, Bool.and_eq_true] at h
  rw [← t.trace.inputCheck_eq h.1]
  exact h.2

end
end ErdosOverlap.Numerics
