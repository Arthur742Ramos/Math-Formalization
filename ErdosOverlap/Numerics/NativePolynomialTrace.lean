module

public import ErdosOverlap.Numerics.NativePolynomialCache
public import ErdosOverlap.Numerics.PolynomialBoxTrace

namespace ErdosOverlap.Native6Leaves

open Numerics
@[expose] public section

theorem Geometry.check_of_traced (g : Geometry)
    (ca : CheckedPatchCache g.pieceA g.grid)
    (cb : CheckedPatchCache g.pieceB (1023-g.grid))
    (ta tb : PolynomialBoxTrace)
    (hv : g.Valid)
    (ha : ta.check ca.val g.patchA g.left g.right = true)
    (hb : tb.check cb.val g.patchB g.left g.right = true)
    (hc : g.cache.tracedCheck ta tb g.patchA g.patchB = true) :
    g.check = true :=
  g.check_of_cached ca cb hv (LeafCache.cachedCheck_of_tracedCheck ha hb hc)

def Geometry.traceCheck (g : Geometry) (ca cb : PolynomialBoxCache)
    (ta tb : PolynomialBoxTrace) : Bool :=
  decide g.Valid &&
  ta.check ca g.patchA g.left g.right &&
  tb.check cb g.patchB g.left g.right &&
  g.cache.tracedCheck ta tb g.patchA g.patchB

theorem Geometry.check_of_traceCheck (g : Geometry)
    (ca : CheckedPatchCache g.pieceA g.grid)
    (cb : CheckedPatchCache g.pieceB (1023-g.grid))
    (ta tb : PolynomialBoxTrace)
    (h : g.traceCheck ca.val cb.val ta tb = true) : g.check = true := by
  simp only [traceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact g.check_of_traced ca cb ta tb h.1.1.1 h.1.1.2 h.1.2 h.2

end
end ErdosOverlap.Native6Leaves
