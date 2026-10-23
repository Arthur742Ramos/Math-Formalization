/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Declared linear constraints act on physical q,V,K, independently of epigraph auxiliaries. -/
module
public import ProtectedSources.RationalIntervalPhysical
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalRepertoireSystem {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    RationalLinearSystem (RationalIntervalRows k m (rationalGridSize M r η) ⊕ I)
      (m+(m*k+(k*k+rationalGridSize M r η*m))) where
  coefficient := Sum.elim (rationalIntervalSystem loK hiK lo hi p M r ρ η).coefficient
    (fun row => rationalFormSum (fun j => rationalFormScale (R.coefficient row j)
      (intervalPhysicalForm k m (rationalGridSize M r η) j)))
  rightSide := Sum.elim (rationalIntervalSystem loK hiK lo hi p M r ρ η).rightSide R.rightSide

theorem rational_interval_repertoire_system_iff {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) :
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x ↔
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).Satisfies x ∧
      R.Satisfies (intervalPhysicalVector x) := by
  change (∀ row, rationalFormEval
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).coefficient row) x ≤
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).rightSide row) ↔ _
  simp only [rationalIntervalRepertoireSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    rational_form_eval_sum,rational_form_eval_scale,interval_physical_form_eval]
  simp only [RationalLinearSystem.Satisfies,rationalFormEval,Sum.forall]

theorem rational_interval_repertoire_real_system_iff {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℝ) :
    (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).RealSatisfies x ↔
    (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x ∧
      R.RealSatisfies (intervalPhysicalVector x) := by
  change (∀ row, rationalFormRealEval
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).coefficient row) x ≤
    ((rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).rightSide row : ℝ)) ↔ _
  simp only [rationalIntervalRepertoireSystem,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    rational_form_real_eval_sum,rational_form_real_eval_scale,interval_physical_real_form_eval]
  simp only [RationalLinearSystem.RealSatisfies,rationalFormRealEval,Sum.forall]

end SparseCompletion
