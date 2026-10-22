/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalAccurate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
structure RationalIntervalParameters (k m : ℕ) (I : Type*) where
  loK : Fin k → Fin k → ℚ
  hiK : Fin k → Fin k → ℚ
  lo : Fin m → Fin k → ℚ
  hi : Fin m → Fin k → ℚ
  p : Fin k → ℚ
  M : ℚ
  r : ℚ
  η : ℚ
  R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))
  positiveBound : 0 < M
  positiveSlack : 0 < η
  anchorNonneg : ∀ a, 0 ≤ p a
  normalized : (∑ a, p a)+r=1
  coreLower : ∀ a b, -M ≤ loK a b
  coreUpper : ∀ a b, hiK a b ≤ M
  crossLower : ∀ i a, -M ≤ lo i a
  crossUpper : ∀ i a, hi i a ≤ M
  orderedCross : ∀ i a, lo i a ≤ hi i a

def RationalIntervalParameters.Compatible {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) : Prop :=
  ∃ (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
      (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ),
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=(d.r : ℝ) ∧ IsSkew K ∧
    (∀ a b, (d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ)) ∧
    (∀ i a, (d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ)) ∧
    IsSkew B ∧ (∀ i j, -(d.M : ℝ) ≤ B i j ∧ B i j ≤ (d.M : ℝ)) ∧
    d.R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)

def RationalIntervalParameters.toModel {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (h : d.Compatible) : RationalIntervalModel k m I where
  loK := d.loK
  hiK := d.hiK
  lo := d.lo
  hi := d.hi
  p := d.p
  M := d.M
  r := d.r
  η := d.η
  R := d.R
  positiveBound := d.positiveBound
  positiveSlack := d.positiveSlack
  anchorNonneg := d.anchorNonneg
  normalized := d.normalized
  coreLower := d.coreLower
  coreUpper := d.coreUpper
  crossLower := d.crossLower
  crossUpper := d.crossUpper
  orderedCross := d.orderedCross
  compatibleNonempty := h

end SparseCompletion
