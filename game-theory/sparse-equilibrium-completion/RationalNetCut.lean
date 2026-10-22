/- AI-assisted formalization under the repository Apache-2.0 license.
Draft: exact net-flow cut identities and a maximum-value certificate from the
computed residual set. No flow finder or termination/complexity is asserted. -/
module
public import RationalReachCut
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_net_flow_internal_sum_zero {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (S : Finset (Fin n)) :
    (∑ u ∈ S, ∑ v ∈ S, F u v)=0 := by
  have he : (∑ u ∈ S, ∑ v ∈ S, F u v)= -(∑ u ∈ S, ∑ v ∈ S, F u v) := by
    calc
      _ = ∑ v ∈ S, ∑ u ∈ S, F u v := Finset.sum_comm
      _ = ∑ v ∈ S, ∑ u ∈ S, -F v u := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_congr rfl (fun u _ => hs u v)
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

theorem rational_net_flow_cut_identity {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (S : Finset (Fin n)) :
    (∑ u ∈ S, ∑ v, F u v)=∑ u ∈ S, ∑ v ∈ Sᶜ, F u v := by
  calc
    _ = ∑ u ∈ S, ((∑ v ∈ S, F u v)+(∑ v ∈ Sᶜ, F u v)) := by
      apply Finset.sum_congr rfl
      intro u _
      exact (Finset.sum_add_sum_compl S (fun v => F u v)).symm
    _ = _ := by
      rw [Finset.sum_add_distrib,rational_net_flow_internal_sum_zero F hs S,zero_add]

theorem rational_net_flow_cut_value {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (s t : Fin n) (S : Finset (Fin n))
    (hsource : s ∈ S) (hsink : t ∉ S)
    (hconserve : ∀ u, u ≠ s → u ≠ t → (∑ v, F u v)=0) :
    (∑ v, F s v)=∑ u ∈ S, ∑ v ∈ Sᶜ, F u v := by
  rw [← rational_net_flow_cut_identity F hs S]
  symm
  apply Finset.sum_eq_single s
  · intro u hu hus
    exact hconserve u hus (fun he => hsink (he ▸ hu))
  · exact fun h => False.elim (h hsource)

theorem rational_net_flow_cut_upper {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (hc : ∀ u v, F u v ≤ C u v)
    (s t : Fin n) (S : Finset (Fin n)) (hsource : s ∈ S) (hsink : t ∉ S)
    (hconserve : ∀ u, u ≠ s → u ≠ t → (∑ v, F u v)=0) :
    (∑ v, F s v) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, C u v := by
  rw [rational_net_flow_cut_value F hs s t S hsource hsink hconserve]
  apply Finset.sum_le_sum
  intro u _
  exact Finset.sum_le_sum (fun v _ => hc u v)

theorem rational_residual_cut_maximum_certificate {n : ℕ}
    (C F G : Fin n → Fin n → ℚ)
    (hFskew : ∀ u v, F u v= -F v u) (hGskew : ∀ u v, G u v= -G v u)
    (hFcap : ∀ u v, F u v ≤ C u v) (hGcap : ∀ u v, G u v ≤ C u v)
    (s t : Fin n)
    (hFconserve : ∀ u, u ≠ s → u ≠ t → (∑ v, F u v)=0)
    (hGconserve : ∀ u, u ≠ s → u ≠ t → (∑ v, G u v)=0)
    (hunreachable : t ∉ residualReachLayers (rationalResidualAdj C F) s n) :
    (∑ v, G s v) ≤ ∑ v, F s v := by
  let S := residualReachLayers (rationalResidualAdj C F) s n
  have hsource : s ∈ S :=
    residual_reach_layers_mono (rationalResidualAdj C F) s (Nat.zero_le n)
      (Finset.mem_singleton_self s)
  have hvalue := rational_net_flow_cut_value F hFskew s t S hsource hunreachable hFconserve
  have hupper := rational_net_flow_cut_upper C G hGskew hGcap s t S hsource hunreachable hGconserve
  have hsat := rational_residual_reachable_cut_saturated C F hFcap s
  change (∑ u ∈ S, ∑ v ∈ Sᶜ, F u v)=(∑ u ∈ S, ∑ v ∈ Sᶜ, C u v) at hsat
  linarith

end SparseCompletion
