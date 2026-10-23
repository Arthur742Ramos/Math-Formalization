/- Meaningful finite actual-value/counter controls. Exact execution status is retained in external immutable receipts.
These evaluate the computed writer and are not independent kernel/bit tests. -/
module
public import CountedGaussianKernel
public meta import CountedGaussianPrimitives
public meta import CountedGaussianKernel
public meta import FlowComputationCost
public meta import CountedFlowInitialization
public meta import RationalGaussianKernel
@[expose] public section
namespace SparseCompletion

def gaussianCostControlVector : Gaussian.QVec 3 :=
  List.Vector.ofFn (fun i => (i.val + 1 : ℕ))
def gaussianCostControlZero : Gaussian.QTable 1 1 := Gaussian.tableOfFn (fun _ _ => 0)
def gaussianCostControlUnit : Gaussian.QTable 1 1 := Gaussian.tableOfFn (fun _ _ => 1)
def gaussianCostControlPair : Gaussian.QTable 1 2 := Gaussian.tableOfFn (fun _ _ => 1)
def gaussianCostControlLate : Gaussian.QTable 1 2 := Gaussian.tableOfFn (fun _ j => if j = 0 then 0 else 1)

#guard (gaussianCountVectorGet gaussianCostControlVector 2).1 = 3
#guard flowWorkTotal (gaussianCountVectorGet gaussianCostControlVector 0).2 = 2
#guard flowWorkTotal (gaussianCountVectorGet gaussianCostControlVector 2).2 = 6
#guard flowWorkTotal (gaussianCountVectorOfFn (fun _ : Fin 2 => ((0 : ℚ), ({} : FlowWork)))).2 = 6
#guard flowWorkTotal (gaussianCountTableOfFn (fun _ _ : Fin 2 => ((0 : ℚ), ({} : FlowWork)))).2 = 18
#guard (gaussianCountFiniteSum (fun i : Fin 3 => ((i.val + 1 : ℕ), ({} : FlowWork)))).1 = 6
#guard flowWorkTotal (gaussianCountFiniteSum (fun _ : Fin 3 => ((0 : ℚ), ({} : FlowWork)))).2 = 50
#guard (gaussianCountFirstNonzero 3 (fun i => ((if i = 2 then 1 else 0 : ℚ), ({} : FlowWork)))).1 = some 2
#guard flowWorkTotal (gaussianCountFirstNonzero 3 (fun _ => ((0 : ℚ), ({} : FlowWork)))).2 = 13
#guard flowWorkTotal (gaussianCountFirstNonzero 3 (fun _ => ((1 : ℚ), ({} : FlowWork)))).2 = 3
#guard flowWorkTotal (gaussianCountFirstNonzero 3 (fun i => ((if i = 2 then 1 else 0 : ℚ), ({} : FlowWork)))).2 = 11
#guard (gaussianCountKernel 1 1 gaussianCostControlZero).1.map List.Vector.toList = some [1]
#guard flowWorkTotal (gaussianCountKernel 1 1 gaussianCostControlZero).2 = 16
#guard (gaussianCountKernel 1 1 gaussianCostControlUnit).1 = none
#guard flowWorkTotal (gaussianCountKernel 1 1 gaussianCostControlUnit).2 = 17
#guard (gaussianCountKernel 1 2 gaussianCostControlPair).1.map List.Vector.toList = some [-1, 1]
#guard flowWorkTotal (gaussianCountKernel 1 2 gaussianCostControlPair).2 = 102
#guard flowWorkTotal (gaussianCountKernel 1 2 gaussianCostControlLate).2 = 19
#guard flowWorkTotal (gaussianCountKernel 0 2 (Gaussian.tableOfFn (fun i _ => Fin.elim0 i))).2 = 11
#guard flowWorkTotal (gaussianCountKernel 1 0 (Gaussian.tableOfFn (fun _ i => Fin.elim0 i))).2 = 1

end SparseCompletion
