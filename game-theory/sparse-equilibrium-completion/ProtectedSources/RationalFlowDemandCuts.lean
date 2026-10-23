/- AI-assisted formalization under the repository Apache-2.0 license.
Exact rational demand-network cut formula. No max-flow existence or polynomial
solver is assumed or asserted. The source/sink capacities are positive and
negative parts of the signed demand. -/
module
public import ProtectedSources.RationalCertificate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalDemandNetworkCut {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (S : Finset (Fin m)) : ℚ :=
  (∑ i ∈ Sᶜ, max (d i) 0)+(∑ i ∈ S, max (-d i) 0)+
    ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j

theorem rational_demand_parts (d : ℚ) : max d 0-max (-d) 0=d := by
  by_cases h : 0 ≤ d
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hh := le_of_not_ge h
    rw [max_eq_right hh,max_eq_left (neg_nonneg.mpr hh)]
    ring

theorem rational_demand_network_cut_identity {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (S : Finset (Fin m)) :
    rationalDemandNetworkCut d c S =
      (∑ i, max (d i) 0)-(∑ i ∈ S, d i)+∑ i ∈ S, ∑ j ∈ Sᶜ, c i j := by
  have hp := Finset.sum_add_sum_compl S (fun i => max (d i) 0)
  have hd : (∑ i ∈ S, max (d i) 0)-(∑ i ∈ S, max (-d i) 0) = ∑ i ∈ S, d i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => rational_demand_parts (d i))
  unfold rationalDemandNetworkCut
  linarith

theorem rational_demand_network_cuts_iff {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) :
    (∀ S : Finset (Fin m), (∑ i, max (d i) 0) ≤ rationalDemandNetworkCut d c S) ↔
      ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j := by
  constructor <;> intro h S
  · have hh := h S
    rw [rational_demand_network_cut_identity] at hh
    linarith
  · rw [rational_demand_network_cut_identity]
    have hh := h S
    linarith

end SparseCompletion
