/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.

Exact fixed-point Horner evaluation.
-/
module

public import ErdosOverlap.Numerics.FixedBoxFast
public import ErdosOverlap.Numerics.FrontierPolynomialDirectTrace

namespace ErdosOverlap.Numerics

@[expose] public section

def FixedBox.hornerBoxesFast (I : FixedBox) : List FixedBox → FixedBox
  | [] => FixedBox.ofRat 0
  | c :: cs => c.add (I.mulFast (FixedBox.hornerBoxesFast I cs))

theorem FixedBox.hornerBoxesFast_eq (I : FixedBox) (cs : List FixedBox) :
    FixedBox.hornerBoxesFast I cs = FixedBox.hornerBoxes I cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [FixedBox.hornerBoxesFast, FixedBox.hornerBoxes, ih,
      FixedBox.mulFast_eq_mul]

def CachedPolynomialTrace.directCheckFast (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) : Bool :=
  t.inputs.check p lo hi && decide (
    t.trace.range.result = FixedBox.hornerBoxesFast t.inputs.range c.coefficients ∧
    t.trace.primitiveLo.result = FixedBox.hornerBoxesFast t.inputs.lo c.primitive ∧
    t.trace.primitiveHi.result = FixedBox.hornerBoxesFast t.inputs.hi c.primitive ∧
    t.trace.weightedLo.result = FixedBox.hornerBoxesFast t.inputs.lo c.weightedPrimitive ∧
    t.trace.weightedHi.result = FixedBox.hornerBoxesFast t.inputs.hi c.weightedPrimitive)

theorem CachedPolynomialTrace.directCheckFast_eq (t : CachedPolynomialTrace)
    (c : PolynomialBoxCache) (p : PolynomialPiece) (lo hi : ℚ) :
    t.directCheckFast c p lo hi = t.directCheck c p lo hi := by
  simp only [CachedPolynomialTrace.directCheckFast,
    CachedPolynomialTrace.directCheck, FixedBox.hornerBoxesFast_eq]

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.FrontierLeaves

open Numerics
@[expose] public section

def Geometry.directTraceCheckFast (g : Geometry) (ca cb : PolynomialBoxCache)
    (ta tb : CachedPolynomialTrace) : Bool :=
  decide g.Valid &&
    ta.directCheckFast ca g.patchA g.left g.right &&
    tb.directCheckFast cb g.patchB g.left g.right &&
    g.cache.tracedCheck ta.trace tb.trace g.patchA g.patchB

theorem Geometry.directTraceCheckFast_eq (g : Geometry)
    (ca cb : PolynomialBoxCache) (ta tb : CachedPolynomialTrace) :
    g.directTraceCheckFast ca cb ta tb = g.directTraceCheck ca cb ta tb := by
  simp only [Geometry.directTraceCheckFast, Geometry.directTraceCheck,
    CachedPolynomialTrace.directCheckFast_eq]

end
end ErdosOverlap.FrontierLeaves
