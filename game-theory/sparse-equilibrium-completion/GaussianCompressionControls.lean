/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalGaussianPaperFlow
public meta import RationalGaussianCompress
public meta import RationalGaussianPaperFeatures
public meta import RationalGaussianPaperFlow
public meta import RationalFeatureDeletion
public meta import RationalTableAugmentation
public meta import RationalGap
@[expose] public section
open SparseCompletion
open scoped BigOperators

private def massRows : Fin 1 → Fin 4 → ℚ := fun _ _ => 1
private def uniform4 : Fin 4 → ℚ := fun _ => 1/4
private def compressed4 : Gaussian.QVec 4 := rationalGaussianCompressVector massRows uniform4
#guard (rationalWeightSupport compressed4.get).card=1
#guard (∑ i, compressed4.get i)=1
#guard ∀ i, 0 ≤ compressed4.get i

private def coordinateRows : Fin 1 → Fin 4 → ℚ := fun _ i => i.val
private def moment4 : Gaussian.QVec 4 := rationalGaussianCompressVectorWithMass coordinateRows uniform4
#guard (rationalWeightSupport moment4.get).card ≤ 2
#guard (∑ i, moment4.get i)=1
#guard (∑ i, moment4.get i*coordinateRows 0 i)=3/2

private def original4 : Fin 4 → ℚ := fun i => if i=0 then 0 else 1/3
private def compressedOriginal : Gaussian.QVec 4 := rationalGaussianCompressVector massRows original4
#guard compressedOriginal.get 0=0
#guard (rationalWeightSupport compressedOriginal.get).card=1

private def D0 : Fin 2 → Fin 0 → ℚ := fun _ a => Fin.elim0 a
private def E0 : Fin 0 → Fin 2 → ℚ := fun a => Fin.elim0 a
private def p0 : Fin 0 → ℚ := fun a => Fin.elim0 a
private def exactPair : Gaussian.QVec 2 × RationalFlowTable 2 :=
  rationalGaussianPaperExactFlow D0 E0 p0 (fun _ => 1/2) 1 1 1
#guard (rationalWeightSupport exactPair.1.get).card=1
#guard (∑ i, exactPair.1.get i)=1
#guard ∀ i j, rationalFlowTableEntry exactPair.2 i j= -rationalFlowTableEntry exactPair.2 j i

private def generalPair : Gaussian.QVec 2 × RationalFlowTable 2 :=
  rationalGaussianPaperGeneralFlow D0 E0 p0 (fun _ => 1/2) 1 1 0 1
#guard (∑ i, generalPair.1.get i)=1
#guard ∀ i, (∑ j, rationalFlowTableEntry generalPair.2 i j*generalPair.1.get j) ≤ 1

private def zeroPair : Gaussian.QVec 2 × RationalFlowTable 2 :=
  rationalGaussianPaperExactFlow D0 E0 p0 (fun _ => 0) 1 0 1
#guard ∀ i, zeroPair.1.get i=0
#guard ∀ i j, rationalFlowTableEntry zeroPair.2 i j=0

-- This feasible exact input creates a strictly positive source demand after
-- the eta shift; the graph algorithm must perform a genuine augmentation.
private def Dpositive : Fin 2 → Fin 1 → ℚ := fun i _ => if i=0 then 1/2 else -1/2
private def ppositive : Fin 1 → ℚ := fun _ => 1/2
private def positivePair : Gaussian.QVec 2 × RationalFlowTable 2 :=
  rationalGaussianPaperExactFlow Dpositive E0 ppositive (fun _ => 1/4) 1 (1/2) (1/16)
#guard ∀ i, positivePair.1.get i=1/4
#guard rationalFlowTableEntry positivePair.2 0 1= -3/4
#guard rationalFlowTableEntry positivePair.2 1 0=3/4
#guard ∀ i, rationalScore Dpositive ppositive i+
  (∑ j, rationalFlowTableEntry positivePair.2 i j*positivePair.1.get j) ≤ 1/16
