/- AI-assisted actual graph-flow/decoder value-height continuation.
Exact compilation/audit status is recorded in source-bound receipts.
The original reviewed uncompiled v1 is preserved in source-graph-output-height-v1.
These are value/encoding bounds, not primitive or whole-pipeline runtime claims.
-/
module
public import RationalGraphFlowOutputHeight
public import RationalDemandGraphNetwork
@[expose] public section
namespace SparseCompletion

theorem rational_demand_capacity_input_height {m H : ℕ}
    (d : Fin m → ℚ) (c : Fin m → Fin m → ℚ)
    (hd : ∀ i, RationalInputHeight (d i) H)
    (hc : ∀ i j, RationalInputHeight (c i j) H) :
    ∀ u v, RationalInputHeight (rationalDemandCapacity d c u v) H := by
  have hz := rational_input_height_zero H
  have hp (i : Fin m) := rational_input_height_max (hd i) hz
  have hn (i : Fin m) := rational_input_height_max (rational_input_height_neg (hd i)) hz
  intro u v
  induction u using Fin.lastCases with
  | last =>
    induction v using Fin.lastCases with
    | last => simpa only [rationalDemandCapacity, Fin.lastCases_last] using hz
    | cast v =>
      induction v using Fin.lastCases with
      | last => simpa [rationalDemandCapacity] using hz
      | cast j => simpa [rationalDemandCapacity] using hp j
  | cast u =>
    induction u using Fin.lastCases with
    | last => simpa [rationalDemandCapacity] using hz
    | cast i =>
      induction v using Fin.lastCases with
      | last => simpa [rationalDemandCapacity] using hz
      | cast v =>
        induction v using Fin.lastCases with
        | last => simpa [rationalDemandCapacity] using hn i
        | cast j => simpa [rationalDemandCapacity] using hc i j

theorem rational_demand_graph_net_output_height {m H : ℕ}
    (d : Fin m → ℚ) (c : Fin m → Fin m → ℚ)
    (hcn : ∀ i j, 0 ≤ c i j)
    (hd : ∀ i, RationalInputHeight (d i) H)
    (hc : ∀ i j, RationalInputHeight (c i j) H) :
    ∀ u v, RationalInputHeight (rationalFlowTableEntry (rationalDemandGraphFindTable d c) u v)
      (rationalGraphFlowHeight (m+2) H) := by
  apply rational_table_graph_flow_output_height
  · simpa only [rational_demand_table_entry] using rational_demand_capacity_nonneg d c hcn
  · simpa only [rational_demand_table_entry] using rational_demand_capacity_input_height d c hd hc

/-- Positive arcs are actual max(net,0) values, hence inherit the earned net
height. A newly chosen arbitrary feasible arc flow is not substituted here. -/
theorem rational_demand_graph_positive_arc_output_height {m H : ℕ}
    (d : Fin m → ℚ) (c : Fin m → Fin m → ℚ)
    (hcn : ∀ i j, 0 ≤ c i j)
    (hd : ∀ i, RationalInputHeight (d i) H)
    (hc : ∀ i j, RationalInputHeight (c i j) H) :
    ∀ i j, RationalInputHeight (rationalDemandGraphFindArc d c i j)
      (rationalGraphFlowHeight (m+2) H) := by
  intro i j
  exact rational_input_height_max
    (rational_demand_graph_net_output_height d c hcn hd hc (demandInternal i) (demandInternal j))
    (rational_input_height_zero _)

def rationalDemandConstructorHeight (H : ℕ) : ℕ := 16*(H+1)

theorem rational_demand_constructed_data_height {m H : ℕ}
    (q t : Fin m → ℚ) (M ε : ℚ)
    (hq : ∀ i, RationalInputHeight (q i) H) (ht : ∀ i, RationalInputHeight (t i) H)
    (hM : RationalInputHeight M H) (hε : RationalInputHeight ε H) :
    (∀ i, RationalInputHeight (q i*(t i-ε)) (rationalDemandConstructorHeight H)) ∧
    ∀ i j, RationalInputHeight (M*q i*q j) (rationalDemandConstructorHeight H) := by
  constructor
  · intro i
    apply rational_input_height_mono (rational_input_height_mul (hq i)
      (rational_input_height_sub (ht i) hε))
    unfold rationalDemandConstructorHeight
    omega
  · intro i j
    apply rational_input_height_mono (rational_input_height_mul
      (rational_input_height_mul hM (hq i)) (hq j))
    unfold rationalDemandConstructorHeight
    omega

def rationalDemandGraphOutputHeight (m H : ℕ) : ℕ :=
  8*rationalGraphFlowHeight (m+2) (rationalDemandConstructorHeight H) + 8*H + 2

/-- Generic literal decoder arithmetic, including 0,-M,+M zero-weight branches.
The nonzero-weight division is total rational division and is bounded directly
from canonical input components, rather than a lower bound supplied on q. -/
theorem rational_flow_decode_with_zeros_input_height {m H S : ℕ}
    (q : Fin m → ℚ) (F : Fin m → Fin m → ℚ) (M : ℚ)
    (hq : ∀ i, RationalInputHeight (q i) H)
    (hF : ∀ i j, RationalInputHeight (F i j) S) (hM : RationalInputHeight M H) :
    ∀ i j, RationalInputHeight (rationalFlowDecodeWithZeros q F M i j) (8*S+8*H+2) := by
  intro i j
  unfold rationalFlowDecodeWithZeros
  split_ifs with hi hj hj
  · exact rational_input_height_zero _
  · exact rational_input_height_mono (rational_input_height_neg hM) (by omega)
  · exact rational_input_height_mono hM (by omega)
  · change RationalInputHeight (-(F i j-F j i)/(q i*q j)) _
    exact rational_input_height_mono
      (rational_input_height_div
        (rational_input_height_neg (rational_input_height_sub (hF i j) (hF j i)))
        (rational_input_height_mul (hq i) (hq j))) (by omega)

/-- Actual final table height from original q,t,M,epsilon input data. The flow
denominator lattice is earned by the direct loop from actual capacities, then
the exact payload/entry theorem connects the decoder to this actual table. -/
theorem rational_demand_graph_completion_table_output_height {m H : ℕ}
    (q t : Fin m → ℚ) (M ε : ℚ)
    (hq : ∀ i, RationalInputHeight (q i) H) (ht : ∀ i, RationalInputHeight (t i) H)
    (hM : RationalInputHeight M H) (hε : RationalInputHeight ε H)
    (hqn : ∀ i, 0 ≤ q i) (hMn : 0 ≤ M) :
    ∀ i j, RationalInputHeight
      (rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε) i j)
      (rationalDemandGraphOutputHeight m H) := by
  obtain ⟨hd, hc⟩ := rational_demand_constructed_data_height q t M ε hq ht hM hε
  have harc := rational_demand_graph_positive_arc_output_height
    (fun i => q i*(t i-ε)) (fun i j => M*q i*q j)
    (fun i j => mul_nonneg (mul_nonneg hMn (hqn i)) (hqn j)) hd hc
  intro i j
  rw [rational_demand_graph_completion_table_entry]
  exact rational_flow_decode_with_zeros_input_height q _ M hq harc hM i j

theorem rational_demand_graph_completion_table_canonical_bits {m H : ℕ}
    (q t : Fin m → ℚ) (M ε : ℚ)
    (hq : ∀ i, RationalInputHeight (q i) H) (ht : ∀ i, RationalInputHeight (t i) H)
    (hM : RationalInputHeight M H) (hε : RationalInputHeight ε H)
    (hqn : ∀ i, 0 ≤ q i) (hMn : 0 ≤ M) :
    ∀ i j, rationalCanonicalEncodingBits
      (rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε) i j) ≤
      2*rationalDemandGraphOutputHeight m H+3 := by
  intro i j
  exact rational_input_height_bits
    (rational_demand_graph_completion_table_output_height q t M ε hq ht hM hε hqn hMn i j)

theorem rational_demand_graph_completion_table_separate_input_height {m Q T B E : ℕ}
    (q t : Fin m → ℚ) (M ε : ℚ)
    (hq : ∀ i, RationalInputHeight (q i) Q) (ht : ∀ i, RationalInputHeight (t i) T)
    (hM : RationalInputHeight M B) (hε : RationalInputHeight ε E)
    (hqn : ∀ i, 0 ≤ q i) (hMn : 0 ≤ M) :
    ∀ i j, RationalInputHeight
      (rationalFlowTableEntry (rationalDemandGraphCompletionTable q t M ε) i j)
      (rationalDemandGraphOutputHeight m (Q+T+B+E)) := by
  apply rational_demand_graph_completion_table_output_height q t M ε
    (fun i => rational_input_height_mono (hq i) (by omega))
    (fun i => rational_input_height_mono (ht i) (by omega))
    (rational_input_height_mono hM (by omega)) (rational_input_height_mono hε (by omega)) hqn hMn

end SparseCompletion
