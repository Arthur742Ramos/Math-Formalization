/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorClass
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_global_accuracy {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          floorIntervalGameValue d s u+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz,he⟩ := floor_interval_game_value_attained d s u hne
  rcases hz with ⟨⟨_,_,hDI,hKI,hB,hBI⟩,hsp,huq,hmass,hK⟩
  obtain ⟨w,hw,hr⟩ := rational_floor_grid_search_accuracy d s u hs hu hR p q K D B
    hsp huq hmass hK (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩)
    (fun i a => ⟨hDI.1 i a,hDI.2 i a⟩) hB hBI δ hδ j ζ hζ
  change exploitability (blockMatrix K D B) (blockWeights p q)=floorIntervalGameValue d s u at he
  rw [he] at hr
  exact ⟨w,hw,hr⟩

end
end SparseCompletion
