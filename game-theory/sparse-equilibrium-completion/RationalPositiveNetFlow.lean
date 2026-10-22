/- AI-assisted formalization under the repository Apache-2.0 license.
Draft: reverse bridge from a capacity-bounded skew net flow to nonnegative
arc flows. This is a representation conversion, not a flow finder. -/
module
public import RationalNetFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalPositiveNetFlow {n : ℕ} (F : Fin n → Fin n → ℚ)
    (u v : Fin n) : ℚ := max (F u v) 0

theorem rational_positive_net_flow_bounds {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hc : ∀ u v, 0 ≤ C u v) (hf : ∀ u v, F u v ≤ C u v) (u v : Fin n) :
    0 ≤ rationalPositiveNetFlow F u v ∧ rationalPositiveNetFlow F u v ≤ C u v := by
  exact ⟨le_max_right _ _,max_le (hf u v) (hc u v)⟩

theorem rational_positive_net_flow_recover {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (u v : Fin n) :
    rationalNetFlow (rationalPositiveNetFlow F) u v=F u v := by
  unfold rationalNetFlow rationalPositiveNetFlow
  rw [hs v u]
  exact rational_demand_parts (F u v)

theorem rational_positive_net_flow_divergence {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hs : ∀ u v, F u v= -F v u) (u : Fin n) :
    (∑ v, rationalPositiveNetFlow F u v)-(∑ v, rationalPositiveNetFlow F v u)=
      ∑ v, F u v := by
  rw [← rational_net_flow_divergence]
  exact Finset.sum_congr rfl (fun v _ => rational_positive_net_flow_recover F hs u v)

end SparseCompletion
