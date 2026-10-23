/- AI-assisted formalization under repository Apache-2.0.
Development graph-fuel demand-network composition; exact check status belongs
to the external source-bound receipts.
The actual direct graph-fuel finder produces the net table used for every
cut, saturation, nonnegative arc and decoded matrix below. The earlier numeric
fuel demand finder is imported for reusable table/cut lemmas only and is never
called by the new executable definitions. No total or bit-runtime claim. -/
module
public import ProtectedSources.RationalDemandNetwork
public import ProtectedSources.RationalTableFlowPolynomial
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalDemandGraphFindTable {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : RationalFlowTable (m+2) :=
  rationalTableFindFlowPolynomial (rationalDemandTable d c) (demandSource m) (demandSink m)

def rationalDemandGraphFuel {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : ℕ := rationalTableGraphFuel (rationalDemandTable d c)

theorem rational_demand_graph_find_table_eq_direct {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) :
    rationalDemandGraphFindTable d c =
      rationalTableFlowIterateDirect (rationalDemandTable d c) (demandSource m) (demandSink m)
        (rationalDemandGraphFuel d c) (rationalZeroFlowTable (m+2)) := rfl

/-- A graph-size bound on actual loop fuel. It does not bound the machine
cost of an attempt, rational bit sizes, materialization or total execution. -/
theorem rational_demand_graph_fuel_bound {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) :
    rationalDemandGraphFuel d c ≤ (m+2)*(m+2)*(m+4)+1 := by
  have hcard : (rationalCapacityArcSupport (rationalDemandTable d c)).card ≤ (m+2)*(m+2) := by
    calc
      _ ≤ Fintype.card (Fin (m+2) × Fin (m+2)) := Finset.card_le_univ _
      _ = _ := by simp
  unfold rationalDemandGraphFuel rationalTableGraphFuel
  have hh := Nat.mul_le_mul_right (m+4) hcard
  simpa only [show m+2+2 = m+4 by omega] using Nat.add_le_add_right hh 1

theorem rational_demand_graph_find_stops {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j) :
    rationalAugmentOnce (rationalDemandTable d c) (rationalDemandGraphFindTable d c)
      (demandSource m) (demandSink m) = none := by
  apply rational_table_find_flow_polynomial_stops
  simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc

def rationalDemandGraphFindArc {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i j : Fin m) : ℚ :=
  rationalPositiveNetFlow (rationalFlowTableEntry (rationalDemandGraphFindTable d c))
    (demandInternal i) (demandInternal j)

def rationalDemandGraphFindSink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) : ℚ :=
  rationalPositiveNetFlow (rationalFlowTableEntry (rationalDemandGraphFindTable d c))
    (demandInternal i) (demandSink m)

theorem rational_demand_graph_find_source_value {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j) :
    rationalTableFlowValue (rationalDemandGraphFindTable d c) (demandSource m) =
      ∑ i, max (d i) 0 := by
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_polynomial_invariant (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC)
  have hcert := rational_table_find_flow_polynomial_cut_certificate (rationalDemandTable d c)
    (demandSource m) (demandSink m) (demand_source_ne_sink m) hC
  dsimp only at hcert
  obtain ⟨hs, ht, he⟩ := hcert
  rw [rational_demand_table_cut d c _ hs ht] at he
  let T := residualReachLayers
    (rationalResidualAdj (rationalFlowTableEntry (rationalDemandTable d c))
      (rationalFlowTableEntry (rationalDemandGraphFindTable d c))) (demandSource m) (m+2)
  have hlo := (rational_demand_network_cuts_iff d c).mpr hcuts (demandInternalSet T)
  have hhi := rational_table_flow_source_upper _ _ _ _ _ hf
  rw [rational_demand_source_upper] at hhi
  change rationalTableFlowValue (rationalDemandGraphFindTable d c) (demandSource m) ≤ _ at hhi
  change rationalTableFlowValue (rationalDemandGraphFindTable d c) (demandSource m) =
    rationalDemandNetworkCut d c (demandInternalSet T) at he
  exact le_antisymm hhi (he ▸ hlo)

theorem rational_demand_graph_find_source_saturated {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j)
    (i : Fin m) :
    rationalFlowTableEntry (rationalDemandGraphFindTable d c) (demandSource m)
      (demandInternal i) = max (d i) 0 := by
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_polynomial_invariant (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC)
  have hsum : (∑ v, (rationalFlowTableEntry (rationalDemandTable d c) (demandSource m) v -
      rationalFlowTableEntry (rationalDemandGraphFindTable d c) (demandSource m) v)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change rationalTableFlowUpper (rationalDemandTable d c) (demandSource m) -
      rationalTableFlowValue (rationalDemandGraphFindTable d c) (demandSource m) = 0
    rw [rational_demand_source_upper, rational_demand_graph_find_source_value d c hc hcuts, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ (Finset.univ : Finset (Fin (m+2)))) =>
      sub_nonneg.mpr (hf.1 (demandSource m) v))).mp hsum
  have hi := hz (demandInternal i) (Finset.mem_univ _)
  simp only [rational_demand_table_entry, demand_capacity_source_internal] at hi
  change max (d i) 0 - rationalFlowTableEntry (rationalDemandGraphFindTable d c)
    (demandSource m) (demandInternal i) = 0 at hi
  exact (sub_eq_zero.mp hi).symm

theorem rational_demand_graph_find_saturated {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j) :
    RationalSaturatedFlow d c (rationalDemandGraphFindArc d c) (rationalDemandGraphFindSink d c) := by
  let F := rationalFlowTableEntry (rationalDemandGraphFindTable d c)
  let P := rationalPositiveNetFlow F
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_polynomial_invariant (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC)
  have hpb : ∀ u v, 0 ≤ P u v ∧ P u v ≤ rationalDemandCapacity d c u v := by
    intro u v
    simpa only [rational_demand_table_entry] using
      rational_positive_net_flow_bounds _ F hC hf.1 u v
  have hpzero : ∀ u v, rationalDemandCapacity d c u v = 0 → P u v = 0 := by
    intro u v hz
    exact le_antisymm (hz ▸ (hpb u v).2) (hpb u v).1
  have hp_source : ∀ i, P (demandSource m) (demandInternal i) = max (d i) 0 := by
    intro i
    dsimp [P, F, rationalPositiveNetFlow]
    rw [rational_demand_graph_find_source_saturated d c hc hcuts]
    exact max_eq_left (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 0 ≤ P (demandInternal i) (demandSink m) ∧
      P (demandInternal i) (demandSink m) ≤ max (-d i) 0
    simpa only [demand_capacity_internal_sink] using hpb (demandInternal i) (demandSink m)
  · intro i j
    change 0 ≤ P (demandInternal i) (demandInternal j) ∧
      P (demandInternal i) (demandInternal j) ≤ c i j
    simpa only [demand_capacity_internal_internal] using hpb (demandInternal i) (demandInternal j)
  · intro i
    have hdiv := rational_positive_net_flow_divergence F hf.2.1 (demandInternal i)
    have hcons : (∑ v, F (demandInternal i) v) = 0 :=
      hf.2.2.1 (demandInternal i) (demand_internal_ne_source i) (demand_internal_ne_sink i)
    rw [hcons] at hdiv
    rw [demand_nodes_sum, demand_nodes_sum] at hdiv
    have h_is := hpzero (demandInternal i) (demandSource m)
      (demand_capacity_to_source d c _)
    have h_ti := hpzero (demandSink m) (demandInternal i)
      (demand_capacity_from_sink d c _)
    change (∑ j, P (demandInternal i) (demandInternal j)) +
      P (demandInternal i) (demandSink m) + P (demandInternal i) (demandSource m) -
      ((∑ j, P (demandInternal j) (demandInternal i)) +
      P (demandSink m) (demandInternal i) + P (demandSource m) (demandInternal i)) = 0 at hdiv
    rw [h_is, h_ti, hp_source i] at hdiv
    change max (d i) 0 + (∑ j, P (demandInternal j) (demandInternal i)) =
      P (demandInternal i) (demandSink m) + ∑ j, P (demandInternal i) (demandInternal j)
    linarith

def rationalDemandGraphCompletion {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) :
    Fin m → Fin m → ℚ :=
  rationalFlowDecodeWithZeros q
    (rationalDemandGraphFindArc (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)) M

theorem rational_demand_graph_completion_sound {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hr : (∑ i, q i) = r)
    (hg : ∀ i, t i ≤ ε+M*r)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, q i*(t i-ε)) ≤
      ∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j) :
    ResidualRatConditions q t M ε (rationalDemandGraphCompletion q t M ε) := by
  exact rational_saturated_flow_completion_with_zeros q t _ _ M r ε hM hq hr hg
    (rational_demand_graph_find_saturated _ _
      (fun i j => mul_nonneg (mul_nonneg hM (hq i)) (hq j)) hcuts)

def rationalDemandGraphFindPayload {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : RationalDemandFlowPayload m :=
  let net := rationalDemandGraphFindTable d c
  let P := rationalPositiveNetFlow (rationalFlowTableEntry net)
  { net := net
    arcF := Vector.ofFn fun i => Vector.ofFn fun j => P (demandInternal i) (demandInternal j)
    sinkY := Vector.ofFn fun i => P (demandInternal i) (demandSink m) }

@[simp] theorem rational_demand_graph_payload_arc {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i j : Fin m) :
    rationalFlowTableEntry (rationalDemandGraphFindPayload d c).arcF i j =
      rationalDemandGraphFindArc d c i j := by
  simp [rationalFlowTableEntry, rationalDemandGraphFindPayload, rationalDemandGraphFindArc,
    cached_vector_get_ofFn]

@[simp] theorem rational_demand_graph_payload_sink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) :
    (rationalDemandGraphFindPayload d c).sinkY.get i = rationalDemandGraphFindSink d c i := by
  simp [rationalDemandGraphFindPayload, rationalDemandGraphFindSink, cached_vector_get_ofFn]

/-- The executable matrix-producing interface. The net finder is run in the
payload construction, followed by finite materialization of the decoded matrix.
No per-operation or polynomial bit-runtime bound is claimed. -/
def rationalDemandGraphCompletionTable {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) :
    RationalFlowTable m :=
  let payload := rationalDemandGraphFindPayload (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)
  Vector.ofFn fun i => Vector.ofFn fun j =>
    rationalFlowDecodeWithZeros q (rationalFlowTableEntry payload.arcF) M i j

theorem rational_demand_graph_completion_table_entry {m : ℕ} (q t : Fin m → ℚ)
    (M ε : ℚ) (i j : Fin m) :
    rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε) i j =
      rationalDemandGraphCompletion q t M ε i j := by
  simp only [rationalDemandGraphCompletionTable, rationalFlowTableEntry, cached_vector_get_ofFn]
  have harc : rationalFlowTableEntry
      (rationalDemandGraphFindPayload (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)).arcF =
      rationalDemandGraphFindArc (fun i => q i*(t i-ε)) (fun i j => M*q i*q j) := by
    funext u v
    exact rational_demand_graph_payload_arc _ _ u v
  change rationalFlowDecodeWithZeros q
      (rationalFlowTableEntry (rationalDemandGraphFindPayload
        (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)).arcF) M i j = _
  rw [harc]
  rfl

theorem rational_demand_graph_completion_table_sound {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hr : (∑ i, q i) = r)
    (hg : ∀ i, t i ≤ ε+M*r)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, q i*(t i-ε)) ≤
      ∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j) :
    ResidualRatConditions q t M ε
      (rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε)) := by
  have he : rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε) =
      rationalDemandGraphCompletion q t M ε := by
    funext i j
    exact rational_demand_graph_completion_table_entry q t M ε i j
  rw [he]
  exact rational_demand_graph_completion_sound q t M r ε hM hq hr hg hcuts

end SparseCompletion
