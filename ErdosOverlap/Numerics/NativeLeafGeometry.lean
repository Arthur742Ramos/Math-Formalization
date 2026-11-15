module

public import ErdosOverlap.Numerics.LeafCache
public import ErdosOverlap.Certificate.Native6AffineData
public import ErdosOverlap.Certificate.Native6KernelData
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Numerics.TaylorUniform

/-! Exact source-linked geometry and reusable arithmetic for native integral leaves. -/

namespace ErdosOverlap.Native6Leaves

open Numerics

@[expose] public section

structure Geometry where
  left : ℚ
  right : ℚ
  pieceA : ℕ
  pieceB : ℕ
  grid : ℕ
  cache : LeafCache
  deriving DecidableEq, Repr

def Geometry.patchA (g : Geometry) : PolynomialPiece :=
  affineKernelPatch (quantizedCoefficients (Native6Grid.coefficientRow g.grid))
    (taylorGridCenter g.grid) taylorGridRadius Native6Data.y0 Native6Data.y2
    (Native6Jumps.pieceAt g.pieceA)

def Geometry.patchB (g : Geometry) : PolynomialPiece :=
  (affineKernelPatch (quantizedCoefficients (Native6Grid.coefficientRow (1023-g.grid)))
    (taylorGridCenter (1023-g.grid)) taylorGridRadius Native6Data.y0 Native6Data.y2
    (Native6Jumps.pieceAt g.pieceB)).reflectTwo

def Geometry.Valid (g : Geometry) : Prop :=
  0 ≤ g.left ∧ g.left < g.right ∧ g.right ≤ 1 ∧
  g.pieceA < 6361 ∧ g.pieceB < 6361 ∧ g.grid < 512 ∧
  (Native6Jumps.pieceAt g.pieceA).left ≤ g.left ∧
  g.right ≤ (Native6Jumps.pieceAt g.pieceA).right ∧
  (Native6Jumps.pieceAt g.pieceB).left ≤ 2-g.right ∧
  2-g.left ≤ (Native6Jumps.pieceAt g.pieceB).right ∧
  taylorGridCenter g.grid-taylorGridRadius ≤ g.left ∧
  g.right ≤ taylorGridCenter g.grid+taylorGridRadius ∧
  taylorGridCenter (1023-g.grid)-taylorGridRadius ≤ 2-g.right ∧
  2-g.left ≤ taylorGridCenter (1023-g.grid)+taylorGridRadius

instance (g : Geometry) : Decidable g.Valid := inferInstanceAs (Decidable
  (0 ≤ g.left ∧ g.left < g.right ∧ g.right ≤ 1 ∧
  g.pieceA < 6361 ∧ g.pieceB < 6361 ∧ g.grid < 512 ∧
  (Native6Jumps.pieceAt g.pieceA).left ≤ g.left ∧
  g.right ≤ (Native6Jumps.pieceAt g.pieceA).right ∧
  (Native6Jumps.pieceAt g.pieceB).left ≤ 2-g.right ∧
  2-g.left ≤ (Native6Jumps.pieceAt g.pieceB).right ∧
  taylorGridCenter g.grid-taylorGridRadius ≤ g.left ∧
  g.right ≤ taylorGridCenter g.grid+taylorGridRadius ∧
  taylorGridCenter (1023-g.grid)-taylorGridRadius ≤ 2-g.right ∧
  2-g.left ≤ taylorGridCenter (1023-g.grid)+taylorGridRadius))

def Geometry.check (g : Geometry) : Bool :=
  decide g.Valid && g.cache.check g.patchA g.patchB g.left g.right

theorem Geometry.patchA_radius (g : Geometry) : g.patchA.radius = 1/1024 := rfl
theorem Geometry.patchB_radius (g : Geometry) : g.patchB.radius = -(1/1024) := rfl

theorem Geometry.check_valid {g : Geometry} (h : g.check = true) : g.Valid := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem Geometry.check_cache {g : Geometry} (h : g.check = true) :
    g.cache.Correct g.patchA g.patchB g.left g.right := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  apply LeafCache.check_sound
  · rw [g.patchA_radius]; norm_num
  · rw [g.patchB_radius]; norm_num
  · exact h.2

/-- Stored geometry carries a kernel proof of its source and arithmetic checks. -/
def CheckedGeometry := {g : Geometry // g.check = true}

theorem CheckedGeometry.valid (g : CheckedGeometry) : g.val.Valid :=
  Geometry.check_valid g.property

theorem CheckedGeometry.cache_correct (g : CheckedGeometry) :
    g.val.cache.Correct g.val.patchA g.val.patchB g.val.left g.val.right :=
  Geometry.check_cache g.property

end
end ErdosOverlap.Native6Leaves
