module

public import ErdosOverlap.Numerics.PolynomialBoxCache
public import ErdosOverlap.Numerics.NativeLeafGeometry

namespace ErdosOverlap.Native6Leaves

open Numerics
@[expose] public section

def sourcePatch (piece grid : ℕ) : PolynomialPiece :=
  affineKernelPatch (quantizedCoefficients (Native6Grid.coefficientRow grid))
    (taylorGridCenter grid) taylorGridRadius Native6Data.y0 Native6Data.y2
    (Native6Jumps.pieceAt piece)

def CheckedPatchCache (piece grid : ℕ) :=
  {c : PolynomialBoxCache // c.check (sourcePatch piece grid) = true}

theorem Geometry.check_of_cached (g : Geometry)
    (ca : CheckedPatchCache g.pieceA g.grid)
    (cb : CheckedPatchCache g.pieceB (1023-g.grid))
    (hv : g.Valid)
    (hc : g.cache.cachedCheck ca.val cb.val g.patchA g.patchB g.left g.right = true) :
    g.check = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hv, ?_⟩
  apply LeafCache.check_of_cachedCheck (ca := ca.val) (cb := cb.val)
  · exact ca.property
  · exact cb.property
  · exact hc

end
end ErdosOverlap.Native6Leaves
