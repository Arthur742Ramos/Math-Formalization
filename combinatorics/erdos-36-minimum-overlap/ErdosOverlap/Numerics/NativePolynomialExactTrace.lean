module

public import ErdosOverlap.Numerics.NativePolynomialCache
public import ErdosOverlap.Numerics.PolynomialInputCache
public import ErdosOverlap.Numerics.PolynomialBoxTracePacket

namespace ErdosOverlap.Native6Leaves

open Numerics
@[expose] public section

def Geometry.exactTraceCheck (g : Geometry) (ca cb : PolynomialBoxCache)
    (ta tb : CachedPolynomialTrace) : Bool :=
  decide g.Valid &&
  ta.check ca g.patchA g.left g.right &&
  tb.check cb g.patchB g.left g.right &&
  g.cache.tracedCheck ta.trace tb.trace g.patchA g.patchB

theorem Geometry.check_of_exactTraceCheck (g : Geometry)
    (ca : CheckedPatchCache g.pieceA g.grid)
    (cb : CheckedPatchCache g.pieceB (1023-g.grid))
    (ta tb : CachedPolynomialTrace)
    (h : g.exactTraceCheck ca.val cb.val ta tb = true) : g.check = true := by
  simp only [exactTraceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  apply g.check_of_cached ca cb h.1.1.1
  exact LeafCache.cachedCheck_of_exactTrace
    (CachedPolynomialTrace.check_sound h.1.1.2)
    (CachedPolynomialTrace.check_sound h.1.2) h.2

end
end ErdosOverlap.Native6Leaves
