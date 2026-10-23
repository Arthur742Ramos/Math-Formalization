/- AI-assisted actual graph-flow/decoder value-height continuation.
Exact compilation/audit status is recorded in source-bound receipts.
The original reviewed uncompiled v1 is preserved in source-graph-output-height-v1.
These are value/encoding bounds, not primitive or whole-pipeline runtime claims.
-/
module
public import ProtectedSources.RationalTableFlowPolynomial
public import ProtectedSources.RationalInputHeight
@[expose] public section
namespace SparseCompletion

theorem rational_matrix_entries_length {n : ℕ} (C : Fin n → Fin n → ℚ) :
    (rationalMatrixEntries C).length = n*n := by
  simp [rationalMatrixEntries, List.length_flatMap, List.length_finRange]

theorem rational_capacity_denominator_from_input_height {n H : ℕ}
    (C : Fin n → Fin n → ℚ) (hC : ∀ u v, RationalInputHeight (C u v) H) :
    rationalCapacityDenominator C ≤ Nat.pow 2 (H*(n*n)) := by
  have hh := rational_denominator_product_power (rationalMatrixEntries C) (Nat.pow 2 H) (by
    intro a ha
    obtain ⟨u, _hu, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨v, _hv, rfl⟩ := List.mem_map.mp ha
    exact (hC u v).2)
  have hp : Nat.pow 2 (H*(n*n)) = Nat.pow (Nat.pow 2 H) (n*n) := Nat.pow_mul 2 H (n*n)
  simpa only [rationalCapacityDenominator, rational_matrix_entries_length, hp] using hh

def rationalGraphFlowHeight (n H : ℕ) : ℕ := H + H*(n*n)

/-- Any actual finite direct run starts at the actual zero table. Its capacity,
skew and lattice invariants are derived from input nonnegativity and capacity
data. No common-denominator conclusion is accepted as a hypothesis. -/
theorem rational_table_direct_flow_output_height {n H : ℕ}
    (C : RationalFlowTable n) (s t : Fin n) (fuel : ℕ)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (hH : ∀ u v, RationalInputHeight (rationalFlowTableEntry C u v) H) :
    ∀ u v, RationalInputHeight
      (rationalFlowTableEntry
        (rationalTableFlowIterateDirect C s t fuel (rationalZeroFlowTable n)) u v)
      (rationalGraphFlowHeight n H) := by
  let D := rationalCapacityDenominator (rationalFlowTableEntry C)
  have hD : 0 < D := rational_capacity_denominator_positive _
  have hDb := rational_capacity_denominator_from_input_height (rationalFlowTableEntry C) hH
  have hinv := rational_table_flow_iterate_direct_invariant C s t D
    (rational_capacity_lattice _) fuel (rationalZeroFlowTable n)
    (rational_zero_flow_table_invariant C s t D hC)
  intro u v
  have hden := (rational_lattice_den_le D hD _ (hinv.2.2.2 u v)).trans hDb
  have hcap : ∀ a b, rationalFlowTableEntry C a b ≤ ((Nat.pow 2 H : ℕ) : ℚ) := by
    intro a b
    exact (le_abs_self _).trans (rational_input_height_magnitude (hH a b))
  have hmag := rational_skew_flow_magnitude (rationalFlowTableEntry C)
    (rationalFlowTableEntry (rationalTableFlowIterateDirect C s t fuel (rationalZeroFlowTable n)))
    hinv.2.1 hinv.1 ((Nat.pow 2 H : ℕ) : ℚ) hcap u v
  constructor
  · exact rational_numerator_binary_bound_from_height _ H (H*(n*n)) hmag hden
  · exact hden.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      unfold rationalGraphFlowHeight
      omega))

theorem rational_table_graph_flow_output_height {n H : ℕ}
    (C : RationalFlowTable n) (s t : Fin n)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (hH : ∀ u v, RationalInputHeight (rationalFlowTableEntry C u v) H) :
    ∀ u v, RationalInputHeight (rationalFlowTableEntry (rationalTableFindFlowPolynomial C s t) u v)
      (rationalGraphFlowHeight n H) :=
  rational_table_direct_flow_output_height C s t (rationalTableGraphFuel C) hC hH

/-- Sharper canonical flow value budget, independently of loop fuel. This is
still a bound on actual values, not a bound on executed operations or bit time. -/
theorem rational_table_graph_flow_canonical_bits {n H : ℕ}
    (C : RationalFlowTable n) (s t : Fin n)
    (hC : ∀ u v, 0 ≤ rationalFlowTableEntry C u v)
    (hH : ∀ u v, RationalInputHeight (rationalFlowTableEntry C u v) H) :
    ∀ u v, rationalCanonicalEncodingBits
      (rationalFlowTableEntry (rationalTableFindFlowPolynomial C s t) u v) ≤ H+2*(H*(n*n))+3 := by
  have hinv := rational_table_find_flow_polynomial_invariant C s t hC
  apply rational_skew_flow_canonical_encoding_bound _ _ hinv.2.1 hinv.1 H (H*(n*n))
    (rationalCapacityDenominator (rationalFlowTableEntry C))
    (rational_capacity_denominator_positive _) (rational_capacity_denominator_from_input_height _ hH)
  · intro u v
    exact (le_abs_self _).trans (rational_input_height_magnitude (hH u v))
  · intro u v
    exact rational_lattice_den_divides _ _ (hinv.2.2.2 u v)

end SparseCompletion
