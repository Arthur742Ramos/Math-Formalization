module
import RationalPaperLPInputHeight
meta import RationalPaperLPInputHeight
open scoped BigOperators
open SparseCompletion

#guard RationalInputHeight (3/7 : ℚ) 3
#guard RationalInputHeight ((-3/7 : ℚ)⁻¹) 3
#guard RationalInputHeight ((3/7 : ℚ)+(-2/5)) 13
#guard RationalInputHeight ((3/7 : ℚ)*(-2/5)) 12

private def sampleK : Fin 1 → Fin 1 → ℚ := fun _ _ => 0
private def sampleD : Fin 2 → Fin 1 → ℚ := fun i _ => if i=0 then 1/3 else -2/5
private def sampleE : Fin 1 → Fin 2 → ℚ := fun _ i => if i=0 then 1/2 else -3/4
private def sampleP : Fin 1 → ℚ := fun _ => 3/7

#guard rationalGridSize 2 (4/3) (1/4) = 4
#guard rationalCanonicalGridSize 2 (4/3) (1/4) = 4
#guard rationalGridSize 1 1 1 = 2 ∧ rationalCanonicalGridSize 1 1 1 = 1
#guard rationalGridNode 2 (4/3) (1/4) 3 = 9/2
#guard rationalEnvelope 2 (4/3) (2*(4/3)-rationalGridNode 2 (4/3) (1/4) 3) = 81/32

#guard ∀ row i, RationalInputHeight
  (rationalGapCoefficient sampleD sampleP 2 (4/3) (1/5) (1/4) row i)
  (rationalFixedAnchorInputHeight 1 3)
#guard ∀ row, RationalInputHeight
  (rationalGapRightSide sampleK sampleD sampleP 2 (4/3) (1/5) (1/4) row)
  (rationalFixedAnchorInputHeight 1 3)
#guard rationalLinearSystemEncodingBits
  (rationalGapSystem sampleK sampleD sampleP 2 (4/3) (1/5) (1/4)) ≤
    (2*2+2+1+4)*(2+1)*(2048*(1+1)*(3+1)+3)

#guard rationalLinearSystemEncodingBits (rationalFeatureKernelSystem
  (rationalPaperFeatures sampleD sampleE
    (fun i => rationalScore sampleD sampleP i-1/5) 2 (4/3) (1/4) 4)
  (fun _ => 1/2) (0 : Fin 2)) ≤
    2*(1+1+4+2+3)*(2+1)*(2048*(1+1)*(3+1)+3)

#guard rationalGridSize 1 1 0 = 1 ∧ rationalCanonicalGridSize 1 1 0 = 0
