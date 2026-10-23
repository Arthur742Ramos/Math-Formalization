/- AI-assisted Gaussian global-height continuation; Apache-2.0.
Exact check status is recorded in source-bound receipts outside this source.
The original uncompiled v1 draft is preserved in source-global-height-v1.
Frozen Gaussian kernel APIs are unchanged. No bit-cost or general LP claim.
-/
module
public import IntegerMinorHeight
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
@[expose] public section
open scoped Matrix
namespace SparseCompletion.Gaussian

/-- A one-row/one-column border of C, indexed by ι ⊕ Unit. The index order
is prefix first, appended entry last, matching the operational Fin.snoc trace. -/
def oneBorder {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℚ)
    (B : Matrix ι (Fin 2) ℚ) (R : Matrix (Fin 2) ι ℚ)
    (D : Matrix (Fin 2) (Fin 2) ℚ) (i j : Fin 2) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℚ :=
  Matrix.fromBlocks C (fun x _ => B x j) (fun _ y => R i y) (fun _ _ => D i j)

/-- Each one-border determinant is the prefix determinant times the
corresponding entry of the two-border Schur complement. k=0 is included. -/
theorem oneBorder_det {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℚ)
    [Invertible C] (B : Matrix ι (Fin 2) ℚ)
    (R : Matrix (Fin 2) ι ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ)
    (i j : Fin 2) :
    (oneBorder C B R D i j).det = C.det * (D - R * ⅟C * B) i j := by
  have hd := Matrix.det_fromBlocks₁₁ C
    (show Matrix ι Unit ℚ from fun x _ => B x j)
    (show Matrix Unit ι ℚ from fun _ y => R i y)
    (show Matrix Unit Unit ℚ from fun _ _ => D i j)
  calc
    (oneBorder C B R D i j).det = C.det * _ := hd
    _ = C.det * (D - R * ⅟C * B) i j := by
      congr 1
      rw [Matrix.det_unique]
      rfl

/-- The actual two-border Sylvester identity, derived rather than required as
an hminor assumption. This is the nonsingular-prefix case required by a genuine
Gaussian run; a general singular-prefix identity is unnecessary for that run. -/
theorem twoBorder_sylvester {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℚ)
    [Invertible C] (B : Matrix ι (Fin 2) ℚ)
    (R : Matrix (Fin 2) ι ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ) :
    (oneBorder C B R D 0 0).det * (oneBorder C B R D 1 1).det -
      (oneBorder C B R D 1 0).det * (oneBorder C B R D 0 1).det =
      C.det * (Matrix.fromBlocks C B R D).det := by
  rw [oneBorder_det, oneBorder_det, oneBorder_det, oneBorder_det,
    Matrix.det_fromBlocks₁₁, Matrix.det_fin_two]
  ring

/-- Consequently the actual Schur pivot update transforms the four one-border
quotients into the two-border quotient, provided the newly chosen pivot is
nonzero. The Sylvester equality is proved above, not supplied by the caller. -/
theorem twoBorder_residual_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℚ) [Invertible C]
    (B : Matrix ι (Fin 2) ℚ) (R : Matrix (Fin 2) ι ℚ)
    (D : Matrix (Fin 2) (Fin 2) ℚ)
    (hC : C.det ≠ 0) (ha : (oneBorder C B R D 0 0).det ≠ 0) :
    (oneBorder C B R D 1 1).det / C.det -
      ((oneBorder C B R D 1 0).det / C.det) *
        (((oneBorder C B R D 0 1).det / C.det) /
          ((oneBorder C B R D 0 0).det / C.det)) =
      (Matrix.fromBlocks C B R D).det / (oneBorder C B R D 0 0).det := by
  exact residual_shared_minor_step _ _ _ _ _ _ ha hC
    (twoBorder_sylvester C B R D)

/- GaussianActualMinors supplies the explicit nested-sum reindexing bridge:
appendTwoEquiv is applied on BOTH determinant axes, so signs cancel exactly.
It then writes the global actual-stage induction and integer casting. Exact check status is recorded in source-bound receipts; these are not
certificates fed to the kernel. -/

end SparseCompletion.Gaussian
