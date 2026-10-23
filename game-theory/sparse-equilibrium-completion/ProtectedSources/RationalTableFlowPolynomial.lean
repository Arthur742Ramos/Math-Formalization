/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY UNCHECKED. Polynomial graph fuel for the existing actual direct
augmentation loop. This is an augmentation-count result, with no claim about
bit complexity of rational arithmetic or total machine runtime.
-/
module
public import ProtectedSources.RationalAugmentationCount
public import ProtectedSources.RationalTableFlowDirect
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- The same direct loop can be viewed as a forward sequence of materialized
states. This lemma identifies that sequence with executing one more attempt
on its previous terminal state. -/
theorem rational_table_flow_iterate_direct_succ_final {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (fuel : ℕ) :
    rationalTableFlowIterateDirect C s t (fuel + 1) F =
      Option.rec (rationalTableFlowIterateDirect C s t fuel F)
        (fun out => out.flow)
        (rationalAugmentOnce C (rationalTableFlowIterateDirect C s t fuel F) s t) := by
  induction fuel generalizing F with
  | zero => rfl
  | succ fuel ih =>
    cases ho : rationalAugmentOnce C F s t with
    | none =>
      rw [rational_table_flow_iterate_direct_of_none C F s t ((fuel + 1) + 1) ho,
        rational_table_flow_iterate_direct_of_none C F s t (fuel + 1) ho, ho]
    | some out =>
      have hhead0 : rationalTableFlowIterateDirect C s t ((fuel + 1) + 1) F =
          rationalTableFlowIterateDirect C s t (fuel + 1) out.flow := by
        change Option.rec (motive := fun _ => RationalFlowTable n) F
          (fun (result : RationalAugmentResult n) =>
            rationalTableFlowIterateDirect C s t (fuel + 1) result.flow)
          (rationalAugmentOnce C F s t) = _
        rw [ho]
      have hhead1 : rationalTableFlowIterateDirect C s t (fuel + 1) F =
          rationalTableFlowIterateDirect C s t fuel out.flow := by
        change Option.rec (motive := fun _ => RationalFlowTable n) F
          (fun (result : RationalAugmentResult n) =>
            rationalTableFlowIterateDirect C s t fuel result.flow)
          (rationalAugmentOnce C F s t) = _
        rw [ho]
      rw [hhead0, hhead1]
      exact ih out.flow

theorem rational_table_flow_iterate_direct_none_persistent {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n) (i j : ℕ) (hij : i ≤ j)
    (hn : rationalAugmentOnce C (rationalTableFlowIterateDirect C s t i F) s t = none) :
    rationalTableFlowIterateDirect C s t j F = rationalTableFlowIterateDirect C s t i F := by
  have haux : ∀ d, rationalTableFlowIterateDirect C s t (i + d) F =
      rationalTableFlowIterateDirect C s t i F := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [show i + (d + 1) = (i + d) + 1 by omega,
        rational_table_flow_iterate_direct_succ_final, ih, hn]
  have he : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa only [he] using haux (j - i)

/-- Input graph size alone supplies the fuel. -/
def rationalTableGraphFuel {n : ℕ} (C : RationalFlowTable n) : ℕ :=
  (rationalCapacityArcSupport C).card * (n + 2) + 1

/-- If the final state were still successful, every earlier state would have
been successful too, because the actual loop stutters permanently after None.
That would contradict the earned capacity-independent trace-count theorem. -/
theorem rational_table_flow_graph_fuel_stops {n : ℕ}
    (C F : RationalFlowTable n) (s t : Fin n)
    (hcap : ∀ u v, rationalFlowTableEntry F u v ≤ rationalFlowTableEntry C u v)
    (hskew : ∀ u v, rationalFlowTableEntry F u v = -rationalFlowTableEntry F v u) :
    rationalAugmentOnce C
      (rationalTableFlowIterateDirect C s t (rationalTableGraphFuel C) F) s t = none := by
  classical
  by_contra hn
  let states : ℕ → RationalFlowTable n := fun i => rationalTableFlowIterateDirect C s t i F
  let outputs : ℕ → RationalAugmentResult n := fun i =>
    (rationalAugmentOnce C (states i) s t).getD
      { path := [], amount := 0, flow := states i }
  have hreturn : ∀ i, i < rationalTableGraphFuel C →
      rationalAugmentOnce C (states i) s t = some (outputs i) := by
    intro i hi
    cases ho : rationalAugmentOnce C (states i) s t with
    | none =>
      have he := rational_table_flow_iterate_direct_none_persistent C F s t i
        (rationalTableGraphFuel C) (le_of_lt hi) ho
      have hn' : rationalAugmentOnce C (states (rationalTableGraphFuel C)) s t ≠ none := hn
      have he' : states (rationalTableGraphFuel C) = states i := he
      exact False.elim (hn' (by rw [he', ho]))
    | some out =>
      simp only [outputs, ho, Option.getD_some]
  have hnext : ∀ i, i < rationalTableGraphFuel C → states (i + 1) = (outputs i).flow := by
    intro i hi
    change rationalTableFlowIterateDirect C s t (i + 1) F = (outputs i).flow
    rw [rational_table_flow_iterate_direct_succ_final]
    change Option.rec (motive := fun _ => RationalFlowTable n) (states i)
      (fun (out : RationalAugmentResult n) => out.flow)
      (rationalAugmentOnce C (states i) s t) = _
    rw [hreturn i hi]
  have hb := rational_successful_trace_length_bound C s t (rationalTableGraphFuel C)
    states outputs hreturn hnext hcap hskew
  unfold rationalTableGraphFuel at hb
  omega

def rationalTableFindFlowPolynomial {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) : RationalFlowTable n :=
  rationalTableFlowIterateDirect C s t (rationalTableGraphFuel C) (rationalZeroFlowTable n)

theorem rational_table_find_flow_polynomial_stops {n : ℕ} (C : RationalFlowTable n)
    (s t : Fin n) (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    rationalAugmentOnce C (rationalTableFindFlowPolynomial C s t) s t = none := by
  apply rational_table_flow_graph_fuel_stops C (rationalZeroFlowTable n) s t
  · intro u v
    simpa only [rational_zero_flow_table_entry] using hC u v
  · intro u v
    simp only [rational_zero_flow_table_entry, neg_zero]

theorem rational_table_flow_iterate_direct_invariant {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (D : ℕ)
    (hC : ∀ u v, RationalDenominatorLattice D (rationalFlowTableEntry C u v))
    (fuel : ℕ) (F : RationalFlowTable n)
    (hF : RationalTableFlowInvariant C F s t D) :
    RationalTableFlowInvariant C (rationalTableFlowIterateDirect C s t fuel F) s t D := by
  rw [rational_table_flow_iterate_direct_eq]
  induction fuel generalizing F with
  | zero => exact hF
  | succ fuel ih =>
    rw [rational_table_flow_iterate_succ]
    cases ho : rationalAugmentOnce C F s t with
    | none => exact hF
    | some out =>
      exact ih out.flow (rational_table_augmentation_invariant C F s t D hC hF out ho)

theorem rational_table_find_flow_polynomial_invariant {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    RationalTableFlowInvariant C (rationalTableFindFlowPolynomial C s t) s t
      (rationalCapacityDenominator (rationalFlowTableEntry C)) :=
  rational_table_flow_iterate_direct_invariant C s t _ (rational_capacity_lattice _)
    (rationalTableGraphFuel C) (rationalZeroFlowTable n)
    (rational_zero_flow_table_invariant C s t _ hC)

theorem rational_table_find_flow_polynomial_unreachable {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    ¬ Relation.ReflTransGen
      (fun u v => rationalResidualAdj (rationalFlowTableEntry C)
        (rationalFlowTableEntry (rationalTableFindFlowPolynomial C s t)) u v = true) s t :=
  (rational_augment_once_none_iff_unreachable C (rationalTableFindFlowPolynomial C s t)
    s t hst).mp (rational_table_find_flow_polynomial_stops C s t hC)

theorem rational_table_find_flow_polynomial_maximum {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (G : Fin n → Fin n → ℚ)
    (hGskew : ∀ u v, G u v = -G v u)
    (hGcap : ∀ u v, G u v ≤ rationalFlowTableEntry C u v)
    (hGcons : ∀ u, u ≠ s → u ≠ t → (∑ v, G u v) = 0) :
    (∑ v, G s v) ≤ rationalTableFlowValue (rationalTableFindFlowPolynomial C s t) s := by
  have hf := rational_table_find_flow_polynomial_invariant C s t hC
  have hn := rational_table_find_flow_polynomial_unreachable C s t hst hC
  apply rational_residual_cut_maximum_certificate (rationalFlowTableEntry C)
    (rationalFlowTableEntry (rationalTableFindFlowPolynomial C s t)) G
    hf.2.1 hGskew hf.1 hGcap s t hf.2.2.1 hGcons
  exact fun h => hn ((residual_reach_layers_iff _ s t).mp h)

theorem rational_table_find_flow_polynomial_cut_certificate {n : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (hst : s ≠ t)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v) :
    let F := rationalTableFindFlowPolynomial C s t
    let S := residualReachLayers
      (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s n
    s ∈ S ∧ t ∉ S ∧
      rationalTableFlowValue F s = ∑ u ∈ S, ∑ v ∈ Sᶜ, rationalFlowTableEntry C u v := by
  dsimp only
  let F := rationalTableFindFlowPolynomial C s t
  let S := residualReachLayers
    (rationalResidualAdj (rationalFlowTableEntry C) (rationalFlowTableEntry F)) s n
  have hf := rational_table_find_flow_polynomial_invariant C s t hC
  have hs : s ∈ S := residual_reach_layers_mono _ s (Nat.zero_le n)
    (Finset.mem_singleton_self s)
  have ht : t ∉ S := fun h => (rational_table_find_flow_polynomial_unreachable C s t hst hC)
    ((residual_reach_layers_iff _ s t).mp h)
  refine ⟨hs, ht, ?_⟩
  have hv := rational_net_flow_cut_value (rationalFlowTableEntry F) hf.2.1 s t S hs ht hf.2.2.1
  have hsat := rational_residual_reachable_cut_saturated (rationalFlowTableEntry C)
    (rationalFlowTableEntry F) hf.1 s
  exact hv.trans hsat

end SparseCompletion
