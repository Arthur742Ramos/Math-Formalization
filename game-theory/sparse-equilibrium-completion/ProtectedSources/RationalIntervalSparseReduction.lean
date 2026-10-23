/- AI-assisted formalization under the repository Apache-2.0 license.
Freeze rational interval recovery before sparsification; no second gap slack. -/
module
public import ProtectedSources.RationalFrozenPhysical
public import ProtectedSources.RationalSparseGapAlgorithm
public import ProtectedSources.RationalIntervalPhysicalProjection
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_physical_recovered_pack {k m H : ℕ}
    (lo hi : Fin m → Fin k → ℚ) (x : Fin (m+(m*k+(k*k+H*m))) → ℚ)
    (hV : ∀ i a, lo i a*intervalQ x i ≤ intervalV x i a ∧
      intervalV x i a ≤ hi i a*intervalQ x i) :
    intervalPhysicalVector x=intervalPack (intervalQ x)
      (fun i a => intervalQ x i*rationalIntervalRecover lo (intervalV x) (intervalQ x) i a)
      (intervalK x) (H := 0) Fin.elim0 := by
  have hprod := rational_interval_recovered_product lo hi (intervalV x) (intervalQ x) hV
  rw [interval_physical_projection]
  congr 1
  funext i a
  exact (hprod i a).symm

theorem rational_interval_sparse_reduction {k m : ℕ} {I : Type} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hx : RationalIntervalPoint loK hiK lo hi (intervalV x) (intervalK x) p (intervalQ x)
      M r ρ η (intervalAux x)) (hR : R.Satisfies (intervalPhysicalVector x)) :
    let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
    ∃ q B, rationalSparseGapAlgorithm (intervalK x) D p M r ρ η
      (rationalFrozenPhysicalSystem (intervalK x) D R)=some (q,B) := by
  let D := rationalIntervalRecover lo (intervalV x) (intervalQ x)
  have hg := (rational_interval_gap_recovered (intervalK x) lo hi (intervalV x) p
    (intervalQ x) M r ρ η hlu
    (rational_interval_point_gap loK hiK lo hi (intervalV x) (intervalK x) p
      (intervalQ x) M r ρ η (intervalAux x) hx).2.2).2
  have hR' : (rationalFrozenPhysicalSystem (intervalK x) D R).Satisfies (intervalQ x) := by
    apply (rational_frozen_physical_system_iff (intervalK x) D R (intervalQ x)).mpr
    rw [←interval_physical_recovered_pack lo hi x hx.2.2.1]
    exact hR
  have hsys : ((rationalGapSystem (intervalK x) D p M r ρ η).append
      (rationalFrozenPhysicalSystem (intervalK x) D R)).Satisfies (intervalQ x) :=
    (rational_linear_append_iff _ _ _).mpr
      ⟨(rational_gap_conditions_iff_linear _ D p _ M r ρ η).mp hg,hR'⟩
  apply rational_sparse_gap_algorithm_complete (intervalK x) D p M r ρ η _ hM hη
    (fun i => (intervalQ (α := ℚ) x i : ℝ))
    ((rational_linear_real_cast_iff _ _).mpr hsys)
    (fun i => by exact_mod_cast hg.1 i)
  exact_mod_cast hg.2.1

end SparseCompletion
