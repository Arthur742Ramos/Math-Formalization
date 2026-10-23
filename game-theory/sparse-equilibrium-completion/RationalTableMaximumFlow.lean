/- AI-assisted formalization under repository Apache-2.0.
Development source; exact-source verification is recorded separately. Actual finite materialized finder returns a
maximum skew capacitated net flow and its computed residual cut certificate.
The executed finder currently uses denominator-based pseudopolynomial fuel;
no capacity-independent iteration, LP polynomial time or bit runtime claim. -/
module
public import RationalTableFlowFuel
public import RationalTableAugmentationComplete
public import RationalNetCut
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_table_find_flow_unreachable {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    ¬ Relation.ReflTransGen
      (fun u v => rationalResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (rationalTableFindFlow C s t)) u v = true) s t :=
  (rational_augment_once_none_iff_unreachable C (rationalTableFindFlow C s t) s t hst).mp
    (rational_table_find_flow_stops C s t hC).2

theorem rational_table_find_flow_maximum {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (G : Fin n → Fin n → ℚ)
    (hGskew : ∀ u v, G u v = -G v u)
    (hGcap : ∀ u v, G u v ≤ rationalFlowTableEntry C u v)
    (hGcons : ∀ u, u ≠ s → u ≠ t → (∑ v, G u v) = 0) :
    (∑ v, G s v) ≤ rationalTableFlowValue (rationalTableFindFlow C s t) s := by
  have hf := (rational_table_find_flow_stops C s t hC).1
  have hn := rational_table_find_flow_unreachable C s t hst hC
  apply rational_residual_cut_maximum_certificate (rationalFlowTableEntry C)
    (rationalFlowTableEntry (rationalTableFindFlow C s t)) G
    hf.2.1 hGskew hf.1 hGcap s t hf.2.2.1 hGcons
  exact fun h => hn ((residual_reach_layers_iff _ s t).mp h)

/-- This cut is computed from the actual returned table. The result is a
verifiable primal/dual equality, not an externally supplied max-flow oracle. -/
theorem rational_table_find_flow_cut_certificate {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    let F := rationalTableFindFlow C s t
    let S := residualReachLayers
      (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s n
    s ∈ S ∧ t ∉ S ∧
      rationalTableFlowValue F s = ∑ u ∈ S, ∑ v ∈ Sᶜ, rationalFlowTableEntry C u v := by
  dsimp only
  let F := rationalTableFindFlow C s t
  let S := residualReachLayers
    (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s n
  have hf := (rational_table_find_flow_stops C s t hC).1
  have hs : s ∈ S := residual_reach_layers_mono _ s (Nat.zero_le n)
    (Finset.mem_singleton_self s)
  have ht : t ∉ S := fun h => (rational_table_find_flow_unreachable C s t hst hC)
    ((residual_reach_layers_iff _ s t).mp h)
  refine ⟨hs, ht, ?_⟩
  have hv := rational_net_flow_cut_value (rationalFlowTableEntry F) hf.2.1 s t S hs ht hf.2.2.1
  have hsat := rational_residual_reachable_cut_saturated (rationalFlowTableEntry C)
    (rationalFlowTableEntry F) hf.1 s
  exact hv.trans hsat

end SparseCompletion
