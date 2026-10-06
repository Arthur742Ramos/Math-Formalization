module
import Solution
open Set Topology TopologicalSpace Metric
universe u
variable {X : Type u} [MetricSpace X]
example (q : ℕ → X) (K : NonemptyCompacts X) :
    OrderArcs.height q K = -∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * infDist (q n) (K : Set X) := rfl
example (A B : NonemptyCompacts X) : OrderArcs.ContinuumInterval A B =
    {K : NonemptyCompacts X // A ≤ K ∧ K ≤ B ∧ IsConnected (K : Set X)} := rfl
example (A B : NonemptyCompacts X) : A < B ↔ (A : Set X) ⊂ (B : Set X) := Iff.rfl
example (γ : unitInterval → NonemptyCompacts X) (h : StrictMono γ) : γ 0 ≠ γ 1 := by
  exact ne_of_lt (h (show (0 : unitInterval) < 1 from zero_lt_one))
example [Subsingleton X] (A B : NonemptyCompacts X) : ¬ A < B := by
  intro h
  have hBA : B ≤ A := by
    intro x _
    obtain ⟨y, hy⟩ := A.nonempty
    change x ∈ (A : Set X)
    rw [Subsingleton.elim x y]
    exact hy
  exact (not_le_of_gt h) hBA

#print axioms OrderArcs.exists_order_arc
#print axioms OrderArcs.height
#print axioms OrderArcs.ContinuumInterval
#print axioms OrderArcs.exists_intermediate_univ
#print axioms OrderArcs.exists_intermediate
#print axioms OrderArcs.exists_infDist_strict
#print axioms OrderArcs.continuous_height
#print axioms OrderArcs.strictMono_height
#print axioms OrderArcs.isClosed_connected_values
#print axioms OrderArcs.isClosed_inclusion
#print axioms OrderArcs.isChain_closure
#print axioms OrderArcs.exists_compact_chain_image
#print axioms OrderArcs.exists_order_arc_in_order
#print axioms BoundaryBumping.closed_component_meets_frontier
