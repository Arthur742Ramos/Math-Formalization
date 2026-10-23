/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalIntervalSparseAlgorithm
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_sparse_algorithm_conditions {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m))))
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (q : Fin m → ℚ) (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalSparseAlgorithm loK hiK lo hi p M r ρ η R=some (q,(K,(D,B)))) :
    R.Satisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0) ∧
    (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
    (∀ i a, lo i a ≤ D i a ∧ D i a ≤ hi i a) ∧
    RationalGapConditions K D p q M r ρ η ∧
    ResidualRatConditions q (rationalScore D p) M (ρ+η) B ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  obtain ⟨x,hpoint,_,hK,hD,hs⟩ := rational_interval_sparse_algorithm_origin
    loK hiK lo hi p M r ρ η R q K D B hout
  have hg := rational_interval_point_gap loK hiK lo hi (intervalV x) (intervalK x) p
    (intervalQ x) M r ρ η (intervalAux x) hpoint
  have hd := (rational_interval_gap_recovered (intervalK x) lo hi (intervalV x) p
    (intervalQ x) M r ρ η hlu hg.2.2).1
  rw [←hK] at hg
  rw [←hD] at hd
  have hh := rational_sparse_gap_algorithm_sound K D p M r ρ η
    (rationalFrozenPhysicalSystem K D R) q B hs
  exact ⟨(rational_frozen_physical_system_iff K D R q).mp hh.1,hg.1,hg.2.1,hd,
    hh.2.1,hh.2.2.1,hh.2.2.2⟩

end SparseCompletion
