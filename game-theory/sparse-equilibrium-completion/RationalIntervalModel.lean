/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalSearch
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalIntervalModel (k m : ℕ) (I : Type*) where
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
  compatibleNonempty : ∃ (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
      (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ),
    (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=(r : ℝ) ∧ IsSkew K ∧
    (∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ)) ∧
    (∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ)) ∧
    IsSkew B ∧ (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
    R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)

theorem rational_interval_model_upper_feasible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) :
    RationalIntervalFeasible d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R := by
  obtain ⟨q,K,D,B,hq,hr,hK,hKb,hD,hB,hBb,hR⟩ := d.compatibleNonempty
  have hpR : ∀ a, 0 ≤ (d.p a : ℝ) := fun a => by exact_mod_cast d.anchorNonneg a
  have hm : (∑ a, blockWeights (fun a => (d.p a : ℝ)) q a)=1 := by
    rw [blockWeights_mass,hr]
    exact_mod_cast d.normalized
  have hKb' : ∀ a b, -(d.M : ℝ) ≤ K a b ∧ K a b ≤ (d.M : ℝ) := by
    intro a b
    exact ⟨le_trans (by exact_mod_cast d.coreLower a b) (hKb a b).1,
      le_trans (hKb a b).2 (by exact_mod_cast d.coreUpper a b)⟩
  have hDb' : ∀ i a, -(d.M : ℝ) ≤ D i a ∧ D i a ≤ (d.M : ℝ) := by
    intro i a
    exact ⟨le_trans (by exact_mod_cast d.crossLower i a) (hD i a).1,
      le_trans (hD i a).2 (by exact_mod_cast d.crossUpper i a)⟩
  have hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (d.p a : ℝ)) q) a ≤ (d.M : ℝ) := by
    intro a
    simpa only [mul_one] using (response_bounds _ _ d.M 1
      (blockWeights_nonneg _ _ hpR hq) hm (blockMatrix_bounds _ _ _ _ hKb' hDb' hBb) a).2
  obtain ⟨x,C,hout⟩ := real_interval_repertoire_algorithm_success d.loK d.hiK d.lo d.hi d.p
    d.M d.r d.M d.η d.R K D q B d.positiveBound d.positiveSlack d.orderedCross
    d.anchorNonneg hq hr hK hKb hD hB hBb hrows hR
  obtain ⟨hpoint,hRx,_⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r d.M d.η d.R x C hout
  exact ⟨x,(rational_interval_repertoire_system_iff d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R x).mpr
    ⟨(rational_interval_system_point d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η x).mpr hpoint,hRx⟩⟩

theorem rational_interval_model_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    ∃ z x B, rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B)) :=
  rational_interval_approximation_complete d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    d.positiveBound d.positiveSlack d.orderedCross (rational_interval_model_upper_feasible d)

end SparseCompletion
