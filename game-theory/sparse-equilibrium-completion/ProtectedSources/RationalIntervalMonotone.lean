/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalPhysicalProjection
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_perspective_call_antitone {m : ℕ}
    (q H : Fin m → ℚ) (ρ ρ' z : ℚ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    rationalPerspectiveCall q H ρ' z ≤ rationalPerspectiveCall q H ρ z := by
  unfold rationalPerspectiveCall
  apply Finset.sum_le_sum
  intro i _
  apply max_le_max _ (le_refl 0)
  have hm := mul_le_mul_of_nonneg_right (add_le_add_right hρ z) (hq i)
  linarith

theorem rational_interval_gap_monotone {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ ρ' η : ℚ) (hρ : ρ ≤ ρ')
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    RationalIntervalGapConditions K lo hi V p q M r ρ' η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hcall⟩
  refine ⟨hq,hm,hV,fun a => le_trans (ha a) hρ,fun i => by linarith [hlo i],?_,?_⟩
  · intro i
    exact le_trans (hcap i) (mul_le_mul_of_nonneg_right (by linarith) (hq i))
  · intro l
    exact le_trans (rational_perspective_call_antitone q _ ρ ρ' _ hq hρ) (hcall l)

theorem rational_interval_repertoire_feasibility_monotone {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Monotone (fun ρ => ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x) := by
  intro ρ ρ' hρ
  rintro ⟨x,hx⟩
  obtain ⟨hbase,hR⟩ := (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ η R x).mp hx
  obtain ⟨hK,hKb,hg⟩ := rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _
    ((rational_interval_system_point loK hiK lo hi p M r ρ η x).mp hbase)
  obtain ⟨A,hA⟩ := (rational_interval_point_epigraph_iff loK hiK lo hi _ _ p _ M r ρ' η).mp
    ⟨hK,hKb,rational_interval_gap_monotone _ lo hi _ p _ M r ρ ρ' η hρ hg⟩
  refine ⟨intervalPack (intervalQ x) (intervalV x) (intervalK x) A,
    (rational_interval_repertoire_system_iff loK hiK lo hi p M r ρ' η R _).mpr ⟨?_,?_⟩⟩
  · apply (rational_interval_system_point loK hiK lo hi p M r ρ' η _).mpr
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA
  · rw [interval_physical_pack]
    simpa only [interval_physical_projection] using hR

end SparseCompletion
