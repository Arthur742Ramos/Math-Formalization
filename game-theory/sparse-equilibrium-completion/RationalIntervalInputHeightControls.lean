module
import RationalRepertoireInputHeight
meta import RationalRepertoireInputHeight
open SparseCompletion
open scoped BigOperators

private def coreLo : Fin 1 → Fin 1 → ℚ := fun _ _ => -1/2
private def coreHi : Fin 1 → Fin 1 → ℚ := fun _ _ => 1/2
private def crossLo : Fin 1 → Fin 1 → ℚ := fun _ _ => -1/3
private def crossHi : Fin 1 → Fin 1 → ℚ := fun _ _ => 2/3
private def anchor : Fin 1 → ℚ := fun _ => 1/2
private def physicalR : RationalLinearSystem (Fin 1) (1+(1*1+(1*1+0*1))) where
  coefficient := fun _ j => if j.val=0 then 1/2 else if j.val=1 then -2/3 else 3/4
  rightSide := fun _ => 5/7
private def intervalS := rationalIntervalSystem coreLo coreHi crossLo crossHi anchor 1 1 (1/4) 1
private def intervalRS := rationalIntervalRepertoireSystem coreLo coreHi crossLo crossHi anchor 1 1 (1/4) 1 physicalR

#guard rationalIntervalVariableCount 1 1 2 = 5
#guard rationalIntervalRowCount 1 1 2 = 18
#guard ∀ row u, RationalInputHeight (intervalS.coefficient row u) 8
#guard ∀ row, RationalInputHeight (intervalS.rightSide row) 8
#guard ∀ row u, RationalInputHeight (intervalRS.coefficient row u) 8
#guard ∀ row, RationalInputHeight (intervalRS.rightSide row) 8
#guard intervalRS.coefficient (.inr 0) 0 = 1/2
#guard intervalRS.coefficient (.inr 0) 1 = -2/3
#guard intervalRS.coefficient (.inr 0) 2 = 3/4
#guard intervalRS.coefficient (.inr 0) 3 = 0 ∧ intervalRS.coefficient (.inr 0) 4 = 0
#guard intervalRS.rightSide (.inr 0) = 5/7
#guard rationalIndexedLinearSystemEncodingBits intervalRS < 100000
#guard ∀ i : Fin 19, Nat.log2 i.val+1 ≤ rationalLPIndexWidth 19

private def noCross : Fin 0 → Fin 0 → ℚ := fun i => Fin.elim0 i
private def noAnchor : Fin 0 → ℚ := Fin.elim0
private def emptyPhysicalR : RationalLinearSystem (Fin 2) (0+(0*0+(0*0+0*0))) where
  coefficient := fun _ j => Fin.elim0 j
  rightSide := fun i => if i=0 then 1 else -1
private def emptyIntervalRS := rationalIntervalRepertoireSystem
  noCross noCross noCross noCross noAnchor 0 0 0 0 emptyPhysicalR

#guard rationalIntervalVariableCount 0 0 1 = 0 ∧ rationalIntervalRowCount 0 0 1 = 3
#guard rationalIndexedLinearSystemEncodingBits emptyIntervalRS = 35
#guard rationalIndexedLinearSystemEncodingBits
  ((rationalGapSystem noCross noCross noAnchor 0 0 0 0).append emptyPhysicalR) = 35
