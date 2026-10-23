/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorValueCertificate
public import ProtectedSources.RationalNoResidualGlobal
@[expose] public section
namespace SparseCompletion

def rationalFloorSearch {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a) (δ ζ : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if 0 < m then rationalAllocationSearch d s hs δ ζ else
    if hk : 0 < k then rationalReservoirSearch d s hs δ ζ ⟨0,hk⟩ else none

noncomputable section

theorem rational_floor_search_value_certificate {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalFloorSearch d s hs δ ζ=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s u+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  cases m with
  | zero =>
    have hk : 0 < k := by
      have hcard := Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Fin k ⊕ Fin 0))
      simp only [Fintype.card_sum,Fintype.card_fin] at hcard
      omega
    have hu0 : u=(Fin.elim0 : Fin 0 → ℚ) := funext fun i => Fin.elim0 i
    subst u
    obtain ⟨w,hw,hlo,hhi⟩ := rational_no_residual_global_certificate d s hs hR hne δ hδ ⟨0,hk⟩ ζ hζ
    refine ⟨w,?_,hlo,hhi⟩
    simpa only [rationalFloorSearch,show ¬0 < (0 : ℕ) by omega,ite_false,dite_eq_left hk] using hw
  | succ m =>
    obtain ⟨w,hw,hlo,hhi⟩ := rational_floor_grid_value_certificate d s u hs hu hR hne δ hδ
      ⟨0,Nat.zero_lt_succ m⟩ ζ hζ
    refine ⟨w,?_,hlo,hhi⟩
    simpa only [rationalFloorSearch,Nat.zero_lt_succ,ite_true] using hw

end
end SparseCompletion
