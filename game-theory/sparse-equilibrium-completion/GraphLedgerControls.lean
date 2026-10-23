/- Executable controls; exact-source outcomes are recorded in separate receipts. -/
module
public import UniformObservationCover
public meta import UniformObservationCover
public import ThresholdStrongLossCover
public section
open SparseCompletion

-- Real finite subset enumeration, rather than a supplied minimum property.
#guard finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := Fin 0)) = 1
#guard finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := Fin 1)) = 2
#guard finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := Fin 2)) = 2
#guard finiteConstraintCoverMinimum (fun _ _ : Fin 0 => false) = 0
#guard twoAnchorObservationEdge (Sum.inl 0 : Fin 2 ⊕ Fin 0) (Sum.inl 1) = true
#guard twoAnchorObservationEdge (Sum.inl 0 : Fin 2 ⊕ Fin 1) (Sum.inr 0) = true
#guard twoAnchorObservationEdge (Sum.inr 0 : Fin 2 ⊕ Fin 2) (Sum.inr 1) = false
#guard twoAnchorObservationEdge (Sum.inl 0 : Fin 2 ⊕ Fin 1) (Sum.inl 0) = false

-- Exact observed zero is constrained, whereas a full missing interval is not.
example : intervalConstraintEdge
    (twoAnchorObservedLo (fun _ _ => 0) (fun (_ : Fin 1) (_ : Fin 2) => (0 : ℝ)) 1)
    (twoAnchorObservedHi (fun _ _ => 0) (fun (_ : Fin 1) (_ : Fin 2) => (0 : ℝ)) 1) 1
    (Sum.inl 0) (Sum.inl 1) := by
  apply (two_anchor_observation_edge_bridge _ _ 1 (by norm_num) _ _).mp
  norm_num [twoAnchorObservationEdge]

example : ¬ intervalStrongLossEdge (fun _ _ : Fin 2 => -1) (fun _ _ : Fin 2 => 1)
    1 0 0 1 := by
  norm_num [intervalStrongLossEdge, intervalLoss]

-- The source threshold is strict: a loss exactly beta may remain uncovered.
example : ¬ intervalStrongLossEdge (fun _ _ : Fin 2 => 0) (fun _ _ : Fin 2 => 0)
    1 1 0 1 := by
  norm_num [intervalStrongLossEdge, intervalLoss]

example : intervalStrongLossEdge (fun _ _ : Fin 2 => 0) (fun _ _ : Fin 2 => 0)
    1 0 0 1 := by
  norm_num [intervalStrongLossEdge, intervalLoss]
