/- AI-assisted formalization under the repository Apache-2.0 license.
Draft: an actual computed residual-reachable set saturates its outgoing cut.
This supplies the reachability/cut bridge; it does not construct a maximum
flow, a path, or an augmentation complexity bound. -/
module
public import ProtectedSources.RationalNetFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_residual_reachable_edge_saturated {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (hf : ∀ u v, F u v ≤ C u v) (s u v : Fin n)
    (hu : u ∈ residualReachLayers (rationalResidualAdj C F) s n)
    (hv : v ∉ residualReachLayers (rationalResidualAdj C F) s n) :
    F u v=C u v := by
  have hn : ¬ 0 < C u v-F u v := by
    intro hp
    apply hv
    apply residual_reach_layers_closed (rationalResidualAdj C F) s u v hu
    simpa only [rationalResidualAdj,decide_eq_true_eq] using hp
  have hh := hf u v
  linarith

theorem rational_residual_reachable_cut_saturated {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (hf : ∀ u v, F u v ≤ C u v) (s : Fin n) :
    (∑ u ∈ residualReachLayers (rationalResidualAdj C F) s n,
      ∑ v ∈ (residualReachLayers (rationalResidualAdj C F) s n)ᶜ, F u v)=
    ∑ u ∈ residualReachLayers (rationalResidualAdj C F) s n,
      ∑ v ∈ (residualReachLayers (rationalResidualAdj C F) s n)ᶜ, C u v := by
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact rational_residual_reachable_edge_saturated C F hf s u v hu (Finset.mem_compl.mp hv)

end SparseCompletion
