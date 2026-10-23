/- AI-assisted formalization under the repository Apache-2.0 license.
Cloud development draft: recursion is demanded only by an actual successful
augmentation. The finite-fuel result equals the preserved state-transformer
implementation. No graph-polynomial augmentation or bit-cost bound is claimed.
-/
module
public import ProtectedSources.RationalTableMaximumFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Unlike a Nat.rec producing an unapplied state transformer, this recursion
inspects the current augmentation before demanding the smaller-fuel call. -/
def rationalTableFlowIterateDirect {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) : ℕ → RationalFlowTable n → RationalFlowTable n
  | 0, F => F
  | fuel + 1, F => Option.rec F
      (fun out => rationalTableFlowIterateDirect C s t fuel out.flow)
      (rationalAugmentOnce C F s t)

theorem rational_table_flow_iterate_direct_eq {n : ℕ} (C F : RationalFlowTable n)
    (s t : Fin n) (fuel : ℕ) :
    rationalTableFlowIterateDirect C s t fuel F =
      rationalTableFlowIterate C s t fuel F := by
  induction fuel generalizing F with
  | zero => rfl
  | succ fuel ih =>
    change Option.rec F
      (fun (out : RationalAugmentResult n) =>
        rationalTableFlowIterateDirect C s t fuel out.flow)
      (rationalAugmentOnce C F s t) = rationalTableFlowIterate C s t (fuel + 1) F
    rw [rational_table_flow_iterate_succ]
    cases ho : rationalAugmentOnce C F s t with
    | none => rfl
    | some out => exact ih out.flow

theorem rational_table_flow_iterate_direct_of_none {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (fuel : ℕ)
    (hn : rationalAugmentOnce C F s t = none) :
    rationalTableFlowIterateDirect C s t fuel F = F := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change Option.rec F
      (fun out => rationalTableFlowIterateDirect C s t fuel out.flow)
      (rationalAugmentOnce C F s t) = F
    rw [hn]

def rationalTableFindFlowDirect {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) : RationalFlowTable n :=
  rationalTableFlowIterateDirect C s t (rationalTableFlowFuel C s)
    (rationalZeroFlowTable n)

theorem rational_table_find_flow_direct_eq {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) :
    rationalTableFindFlowDirect C s t = rationalTableFindFlow C s t :=
  rational_table_flow_iterate_direct_eq C (rationalZeroFlowTable n) s t
    (rationalTableFlowFuel C s)

theorem rational_table_find_flow_direct_stops {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    RationalTableFlowInvariant C (rationalTableFindFlowDirect C s t) s t
      (rationalCapacityDenominator (rationalFlowTableEntry C)) ∧
      rationalAugmentOnce C (rationalTableFindFlowDirect C s t) s t = none := by
  rw [rational_table_find_flow_direct_eq]
  exact rational_table_find_flow_stops C s t hC

theorem rational_table_find_flow_direct_maximum {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (G : Fin n → Fin n → ℚ)
    (hGskew : ∀ u v, G u v = -G v u)
    (hGcap : ∀ u v, G u v ≤ rationalFlowTableEntry C u v)
    (hGcons : ∀ u, u ≠ s → u ≠ t → (∑ v, G u v) = 0) :
    (∑ v, G s v) ≤ rationalTableFlowValue (rationalTableFindFlowDirect C s t) s := by
  rw [rational_table_find_flow_direct_eq]
  exact rational_table_find_flow_maximum C s t hst hC G hGskew hGcap hGcons

theorem rational_table_find_flow_direct_cut_certificate {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    let F := rationalTableFindFlowDirect C s t
    let S := residualReachLayers
      (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s n
    s ∈ S ∧ t ∉ S ∧
      rationalTableFlowValue F s =
        ∑ u ∈ S, ∑ v ∈ Sᶜ, rationalFlowTableEntry C u v := by
  simpa only [rational_table_find_flow_direct_eq] using
    rational_table_find_flow_cut_certificate C s t hst hC

end SparseCompletion
