/- SOURCE-ONLY asserted runtime fixture preparation. Not executed. -/
module
public import RationalGaussianGraphOutputHeight
public meta import RationalTableFlowPolynomial
public meta import RationalDemandGraphNetwork
public meta import RationalGaussianCompress
public meta import RationalFlowEncodingBounds
public meta import RationalDemandGraphOutputHeight
public section
open SparseCompletion

private def checkGraphHeightControl (label : String) (ok : Bool) : IO Unit := do
  if ok then IO.println (label ++ ": PASS") else throw (IO.userError (label ++ ": FAIL"))

#eval checkGraphHeightControl "actual half-capacity skew flow"
  (let C : RationalFlowTable 2 := Vector.ofFn fun u => Vector.ofFn fun v =>
      if u = 0 ∧ v = 1 then 1/2 else 0
   let F := rationalTableFindFlowPolynomial C 0 1
   decide (rationalFlowTableEntry F 0 1 = 1/2 ∧ rationalFlowTableEntry F 1 0 = -1/2))

#eval checkGraphHeightControl "actual positive arcs use max"
  (let d : Fin 2 → ℚ := fun i => if i = 0 then 1 else -1
   let c : Fin 2 → Fin 2 → ℚ := fun _ _ => 1
   decide (rationalDemandGraphFindArc d c 0 1 = 1 ∧ rationalDemandGraphFindArc d c 1 0 = 0))

#eval checkGraphHeightControl "zero weight decoder branches"
  (let q : Fin 2 → ℚ := fun i => if i = 0 then 0 else 1
   let B := rationalDemandGraphCompletionTable q (fun _ => 0) 3 0
   decide (rationalFlowTableEntry B 0 0 = 0 ∧ rationalFlowTableEntry B 0 1 = -3 ∧
     rationalFlowTableEntry B 1 0 = 3))

#eval checkGraphHeightControl "actual positive-weight decoded skew table"
  (let t : Fin 2 → ℚ := fun i => if i = 0 then 1 else -1
   let B := rationalDemandGraphCompletionTable (fun _ => 1) t 1 0
   decide (rationalFlowTableEntry B 0 1 = -1 ∧ rationalFlowTableEntry B 1 0 = 1))

#eval checkGraphHeightControl "actual compressed weights feed actual decoder"
  (let A : Fin 1 → Fin 2 → ℚ := fun _ _ => 1
   let q := (rationalGaussianCompressVector A (fun _ => 1)).get
   let B := rationalDemandGraphCompletionTable q (fun _ => 0) 3 0
   decide (q 0 = 2 ∧ q 1 = 0 ∧ rationalFlowTableEntry B 0 1 = 3 ∧
     rationalFlowTableEntry B 1 0 = -3))

#eval checkGraphHeightControl "actual output canonical budget"
  (let q : Fin 2 → ℚ := fun i => if i = 0 then 0 else 1
   let B := rationalDemandGraphCompletionTable q (fun _ => 0) 3 0
   decide (∀ i j, rationalCanonicalEncodingBits (rationalFlowTableEntry B i j) ≤
     2*rationalDemandGraphOutputHeight 2 2+3))
