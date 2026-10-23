module
import RationalDemandGraphNetwork
meta import RationalDemandGraphNetwork
open scoped BigOperators
open SparseCompletion

-- Each assertion evaluates the materialized result from the actual finder.
def smokeGraphMatrix {m : ℕ} (q t : Fin m → ℚ) (M ε : ℚ) : List (List ℚ) :=
  let B := rationalDemandGraphCompletionTable q t M ε
  List.ofFn fun i => List.ofFn fun j => rationalFlowTableEntry B i j

-- Positive-demand transfer.
#guard smokeGraphMatrix (fun _ : Fin 2 => 1) (fun k => if k = 0 then 1 else -1) 1 0 =
  [[0, -1], [1, 0]]

-- A zero-weight row is reconstructed using the global row convention.
#guard smokeGraphMatrix (fun k : Fin 2 => if k = 0 then 0 else 1)
  (fun k => if k = 0 then 1 else 0) 1 0 = [[0, -1], [1, 0]]

-- Zero bound and zero demand.
#guard smokeGraphMatrix (fun _ : Fin 2 => 1) (fun _ => 0) 0 0 = [[0, 0], [0, 0]]

-- Empty residual vertex set.
#guard smokeGraphMatrix (fun _ : Fin 0 => 0) (fun _ => 0) 0 0 = []

-- The bound depends on graph support, not numeric capacity magnitudes.
#guard rationalDemandGraphFuel (fun i : Fin 2 => if i = 0 then 1 else -1)
  (fun _ _ => 1) = 49
#guard rationalDemandGraphFuel (fun i : Fin 2 => if i = 0 then 1000000000 else -1000000000)
  (fun _ _ => 1000000000) = 49
#guard rationalDemandGraphFuel (fun _ : Fin 2 => 0) (fun _ _ => 0) = 1
#guard rationalDemandGraphFuel (fun _ : Fin 0 => 0) (fun _ _ => 0) = 1
