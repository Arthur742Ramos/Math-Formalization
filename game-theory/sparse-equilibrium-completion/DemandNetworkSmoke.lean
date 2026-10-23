module
import RationalDemandNetwork
meta import RationalDemandNetwork
open scoped BigOperators
open SparseCompletion

-- Each assertion evaluates the materialized result from the actual finder.
def smokeMatrix {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) : List (List ℚ) :=
  let B := rationalDemandCompletionTable q t M ε
  List.ofFn fun i => List.ofFn fun j => rationalFlowTableEntry B i j

-- Positive-demand transfer.
#guard smokeMatrix (fun _ : Fin 2 => 1) (fun k => if k = 0 then 1 else -1) 1 0 =
  [[0, -1], [1, 0]]

-- A zero-weight row is reconstructed using the global row convention.
#guard smokeMatrix (fun k : Fin 2 => if k = 0 then 0 else 1)
  (fun k => if k = 0 then 1 else 0) 1 0 = [[0, -1], [1, 0]]

-- Zero bound and zero demand.
#guard smokeMatrix (fun _ : Fin 2 => 1) (fun _ => 0) 0 0 = [[0, 0], [0, 0]]

-- Empty residual vertex set.
#guard smokeMatrix (fun _ : Fin 0 => 0) (fun _ => 0) 0 0 = []

#print axioms rational_demand_completion_sound
#print axioms rational_demand_find_saturated
#print axioms rational_demand_completion_table_sound
