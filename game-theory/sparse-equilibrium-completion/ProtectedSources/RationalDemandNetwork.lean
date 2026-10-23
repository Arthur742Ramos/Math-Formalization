/- AI-assisted formalization under repository Apache-2.0.
Actual demand-network table and cut reduction. No polynomial runtime claim. -/
module
public import ProtectedSources.RationalTableFlowDirect
public import ProtectedSources.RationalFlowZeroRows
public import ProtectedSources.RationalPositiveNetFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def demandSource (m : ℕ) : Fin (m+2) := Fin.last (m+1)
def demandSink (m : ℕ) : Fin (m+2) := (Fin.last m).castSucc
def demandInternal {m : ℕ} (i : Fin m) : Fin (m+2) := i.castSucc.castSucc

def rationalDemandCapacity {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : Fin (m+2) → Fin (m+2) → ℚ :=
  Fin.lastCases (Fin.lastCases 0 (Fin.lastCases 0 (fun j => max (d j) 0)))
    (Fin.lastCases (fun _ => 0)
      (fun i => Fin.lastCases 0 (Fin.lastCases (max (-d i) 0) (c i))))

def rationalDemandTable {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : RationalFlowTable (m+2) :=
  Vector.ofFn fun u => Vector.ofFn fun v => rationalDemandCapacity d c u v

@[simp] theorem rational_demand_table_entry {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (u v : Fin (m+2)) :
    rationalFlowTableEntry (rationalDemandTable d c) u v =
      rationalDemandCapacity d c u v := by
  simp [rationalFlowTableEntry, rationalDemandTable, cached_vector_get_ofFn]

@[simp] theorem demand_capacity_source_internal {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) :
    rationalDemandCapacity d c (demandSource m) (demandInternal i) = max (d i) 0 := by
  simp [rationalDemandCapacity, demandSource, demandInternal]
@[simp] theorem demand_capacity_internal_sink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) :
    rationalDemandCapacity d c (demandInternal i) (demandSink m) = max (-d i) 0 := by
  simp [rationalDemandCapacity, demandSink, demandInternal]
@[simp] theorem demand_capacity_internal_internal {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i j : Fin m) :
    rationalDemandCapacity d c (demandInternal i) (demandInternal j) = c i j := by
  simp [rationalDemandCapacity, demandInternal]
@[simp] theorem demand_capacity_to_source {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (u : Fin (m+2)) :
    rationalDemandCapacity d c u (demandSource m) = 0 := by
  induction u using Fin.lastCases with
  | last => simp [rationalDemandCapacity, demandSource]
  | cast u =>
    induction u using Fin.lastCases <;> simp [rationalDemandCapacity, demandSource]
@[simp] theorem demand_capacity_from_sink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (v : Fin (m+2)) :
    rationalDemandCapacity d c (demandSink m) v = 0 := by
  simp [rationalDemandCapacity, demandSink]
@[simp] theorem demand_capacity_source_sink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) :
    rationalDemandCapacity d c (demandSource m) (demandSink m) = 0 := by
  simp [rationalDemandCapacity, demandSource, demandSink]

theorem demand_nodes_sum {m : ℕ} (f : Fin (m+2) → ℚ) :
    (∑ v, f v) = (∑ i, f (demandInternal i)) +
      f (demandSink m) + f (demandSource m) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  rfl

def demandInternalSet {m : ℕ} (T : Finset (Fin (m+2))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => demandInternal i ∈ T)

@[simp] theorem mem_demand_internal_set {m : ℕ} (T : Finset (Fin (m+2))) (i : Fin m) :
    i ∈ demandInternalSet T ↔ demandInternal i ∈ T := by simp [demandInternalSet]

theorem demand_nodes_subset_sum {m : ℕ} (T : Finset (Fin (m+2)))
    (f : Fin (m+2) → ℚ) :
    (∑ v ∈ T, f v) = (∑ i ∈ demandInternalSet T, f (demandInternal i)) +
      (if demandSink m ∈ T then f (demandSink m) else 0) +
      (if demandSource m ∈ T then f (demandSource m) else 0) := by
  classical
  have h : (∑ v ∈ T, f v) = ∑ v, if v ∈ T then f v else 0 := by
    simp
  rw [h, demand_nodes_sum]
  simp [demandInternalSet, Finset.sum_filter]

theorem demand_internal_set_compl {m : ℕ} (T : Finset (Fin (m+2))) :
    demandInternalSet Tᶜ = (demandInternalSet T)ᶜ := by
  ext i
  simp

theorem rational_demand_capacity_nonneg {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j) :
    ∀ u v, 0 ≤ rationalDemandCapacity d c u v := by
  intro u v
  induction u using Fin.lastCases with
  | last =>
    induction v using Fin.lastCases with
    | last => simp [rationalDemandCapacity]
    | cast v =>
      induction v using Fin.lastCases <;> simp [rationalDemandCapacity]
  | cast u =>
    induction u using Fin.lastCases with
    | last => simp [rationalDemandCapacity]
    | cast i =>
      induction v using Fin.lastCases with
      | last => simp [rationalDemandCapacity]
      | cast v =>
        induction v using Fin.lastCases <;> simp [rationalDemandCapacity, hc]

theorem rational_demand_table_cut {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (T : Finset (Fin (m+2)))
    (hs : demandSource m ∈ T) (ht : demandSink m ∉ T) :
    (∑ u ∈ T, ∑ v ∈ Tᶜ, rationalFlowTableEntry (rationalDemandTable d c) u v) =
      rationalDemandNetworkCut d c (demandInternalSet T) := by
  classical
  simp only [rational_demand_table_entry]
  rw [demand_nodes_subset_sum T]
  simp only [hs, ht, ite_true, ite_false, add_zero]
  simp_rw [demand_nodes_subset_sum Tᶜ, demand_internal_set_compl]
  simp only [Finset.mem_compl, hs, ht, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, demand_capacity_to_source,
    demand_capacity_source_sink, demand_capacity_internal_sink,
    demand_capacity_internal_internal, demand_capacity_source_internal,
    add_zero]
  unfold rationalDemandNetworkCut
  rw [Finset.sum_add_distrib]
  ring

@[simp] theorem demand_source_ne_sink (m : ℕ) : demandSource m ≠ demandSink m := by
  intro h
  have hv := congrArg Fin.val h
  simp only [demandSource, demandSink, Fin.val_last, Fin.val_castSucc] at hv
  omega
@[simp] theorem demand_internal_ne_source {m : ℕ} (i : Fin m) :
    demandInternal i ≠ demandSource m := by simp [demandInternal, demandSource]
@[simp] theorem demand_internal_ne_sink {m : ℕ} (i : Fin m) :
    demandInternal i ≠ demandSink m := by simp [demandInternal, demandSink]

theorem rational_demand_source_upper {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) :
    rationalTableFlowUpper (rationalDemandTable d c) (demandSource m) =
      ∑ i, max (d i) 0 := by
  unfold rationalTableFlowUpper
  simp only [rational_demand_table_entry]
  rw [demand_nodes_sum]
  simp

def rationalDemandFindTable {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : RationalFlowTable (m+2) :=
  rationalTableFindFlowDirect (rationalDemandTable d c) (demandSource m) (demandSink m)

def rationalDemandFindArc {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i j : Fin m) : ℚ :=
  rationalPositiveNetFlow (rationalFlowTableEntry (rationalDemandFindTable d c))
    (demandInternal i) (demandInternal j)

def rationalDemandFindSink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) : ℚ :=
  rationalPositiveNetFlow (rationalFlowTableEntry (rationalDemandFindTable d c))
    (demandInternal i) (demandSink m)

theorem rational_demand_find_source_value {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j) :
    rationalTableFlowValue (rationalDemandFindTable d c) (demandSource m) =
      ∑ i, max (d i) 0 := by
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_direct_stops (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC).1
  have hcert := rational_table_find_flow_direct_cut_certificate (rationalDemandTable d c)
    (demandSource m) (demandSink m) (demand_source_ne_sink m) hC
  dsimp only at hcert
  obtain ⟨hs, ht, he⟩ := hcert
  rw [rational_demand_table_cut d c _ hs ht] at he
  let T := residualReachLayers
    (rationalResidualAdj (rationalFlowTableEntry (rationalDemandTable d c))
      (rationalFlowTableEntry (rationalDemandFindTable d c))) (demandSource m) (m+2)
  have hlo := (rational_demand_network_cuts_iff d c).mpr hcuts (demandInternalSet T)
  have hhi := rational_table_flow_source_upper _ _ _ _ _ hf
  rw [rational_demand_source_upper] at hhi
  change rationalTableFlowValue (rationalDemandFindTable d c) (demandSource m) ≤ _ at hhi
  change rationalTableFlowValue (rationalDemandFindTable d c) (demandSource m) =
    rationalDemandNetworkCut d c (demandInternalSet T) at he
  exact le_antisymm hhi (he ▸ hlo)

theorem rational_demand_find_source_saturated {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j)
    (i : Fin m) :
    rationalFlowTableEntry (rationalDemandFindTable d c) (demandSource m)
      (demandInternal i) = max (d i) 0 := by
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_direct_stops (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC).1
  have hsum : (∑ v, (rationalFlowTableEntry (rationalDemandTable d c) (demandSource m) v -
      rationalFlowTableEntry (rationalDemandFindTable d c) (demandSource m) v)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change rationalTableFlowUpper (rationalDemandTable d c) (demandSource m) -
      rationalTableFlowValue (rationalDemandFindTable d c) (demandSource m) = 0
    rw [rational_demand_source_upper, rational_demand_find_source_value d c hc hcuts, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ (Finset.univ : Finset (Fin (m+2)))) =>
      sub_nonneg.mpr (hf.1 (demandSource m) v))).mp hsum
  have hi := hz (demandInternal i) (Finset.mem_univ _)
  simp only [rational_demand_table_entry, demand_capacity_source_internal] at hi
  change max (d i) 0 - rationalFlowTableEntry (rationalDemandFindTable d c)
    (demandSource m) (demandInternal i) = 0 at hi
  exact (sub_eq_zero.mp hi).symm

theorem rational_demand_find_saturated {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (hc : ∀ i j, 0 ≤ c i j)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, d i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j) :
    RationalSaturatedFlow d c (rationalDemandFindArc d c) (rationalDemandFindSink d c) := by
  let F := rationalFlowTableEntry (rationalDemandFindTable d c)
  let P := rationalPositiveNetFlow F
  have hC : ∀ u v, 0 ≤ rationalFlowTableEntry (rationalDemandTable d c) u v := by
    simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hc
  have hf := (rational_table_find_flow_direct_stops (rationalDemandTable d c)
    (demandSource m) (demandSink m) hC).1
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
    rw [rational_demand_find_source_saturated d c hc hcuts]
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

def rationalDemandCompletion {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) :
    Fin m → Fin m → ℚ :=
  rationalFlowDecodeWithZeros q
    (rationalDemandFindArc (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)) M

theorem rational_demand_completion_sound {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hr : (∑ i, q i) = r)
    (hg : ∀ i, t i ≤ ε+M*r)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, q i*(t i-ε)) ≤
      ∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j) :
    ResidualRatConditions q t M ε (rationalDemandCompletion q t M ε) := by
  exact rational_saturated_flow_completion_with_zeros q t _ _ M r ε hM hq hr hg
    (rational_demand_find_saturated _ _
      (fun i j => mul_nonneg (mul_nonneg hM (hq i)) (hq j)) hcuts)

/-- Finite data payload. The constructor binds the actual returned net table
before materializing every internal arc and sink entry. Consumers should bind
this payload once and read its vectors, rather than call a getter afresh. -/
structure RationalDemandFlowPayload (m : ℕ) where
  net : RationalFlowTable (m+2)
  arcF : RationalFlowTable m
  sinkY : Vector ℚ m

def rationalDemandFindPayload {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) : RationalDemandFlowPayload m :=
  let net := rationalDemandFindTable d c
  let P := rationalPositiveNetFlow (rationalFlowTableEntry net)
  { net := net
    arcF := Vector.ofFn fun i => Vector.ofFn fun j => P (demandInternal i) (demandInternal j)
    sinkY := Vector.ofFn fun i => P (demandInternal i) (demandSink m) }

@[simp] theorem rational_demand_payload_arc {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i j : Fin m) :
    rationalFlowTableEntry (rationalDemandFindPayload d c).arcF i j =
      rationalDemandFindArc d c i j := by
  simp [rationalFlowTableEntry, rationalDemandFindPayload, rationalDemandFindArc,
    cached_vector_get_ofFn]

@[simp] theorem rational_demand_payload_sink {m : ℕ} (d : Fin m → ℚ)
    (c : Fin m → Fin m → ℚ) (i : Fin m) :
    (rationalDemandFindPayload d c).sinkY.get i = rationalDemandFindSink d c i := by
  simp [rationalDemandFindPayload, rationalDemandFindSink, cached_vector_get_ofFn]

/-- The executable matrix-producing interface. The net finder is run in the
payload construction, followed by finite materialization of the decoded matrix.
No per-operation or polynomial bit-runtime bound is claimed. -/
def rationalDemandCompletionTable {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) :
    RationalFlowTable m :=
  let payload := rationalDemandFindPayload (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)
  Vector.ofFn fun i => Vector.ofFn fun j =>
    rationalFlowDecodeWithZeros q (rationalFlowTableEntry payload.arcF) M i j

theorem rational_demand_completion_table_entry {m : ℕ} (q t : Fin m → ℚ)
    (M ε : ℚ) (i j : Fin m) :
    rationalFlowTableEntry (rationalDemandCompletionTable q t M ε) i j =
      rationalDemandCompletion q t M ε i j := by
  simp only [rationalDemandCompletionTable, rationalFlowTableEntry, cached_vector_get_ofFn]
  have harc : rationalFlowTableEntry
      (rationalDemandFindPayload (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)).arcF =
      rationalDemandFindArc (fun i => q i*(t i-ε)) (fun i j => M*q i*q j) := by
    funext u v
    exact rational_demand_payload_arc _ _ u v
  change rationalFlowDecodeWithZeros q
      (rationalFlowTableEntry (rationalDemandFindPayload
        (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)).arcF) M i j = _
  rw [harc]
  rfl

theorem rational_demand_completion_table_sound {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hr : (∑ i, q i) = r)
    (hg : ∀ i, t i ≤ ε+M*r)
    (hcuts : ∀ S : Finset (Fin m), (∑ i ∈ S, q i*(t i-ε)) ≤
      ∑ i ∈ S, ∑ j ∈ Sᶜ, M*q i*q j) :
    ResidualRatConditions q t M ε
      (rationalFlowTableEntry (rationalDemandCompletionTable q t M ε)) := by
  have he : rationalFlowTableEntry (rationalDemandCompletionTable q t M ε) =
      rationalDemandCompletion q t M ε := by
    funext i j
    exact rational_demand_completion_table_entry q t M ε i j
  rw [he]
  exact rational_demand_completion_sound q t M r ε hM hq hr hg hcuts

end SparseCompletion
