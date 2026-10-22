/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalLinearSolver
public meta import RationalLinearSolver
@[expose] public section
namespace SparseCompletion

def infeasibleConstant : RationalLinearSystem (Fin 1) 0 := ⟨fun _ i => Fin.elim0 i,fun _ => -1⟩
def conflictingBounds : RationalLinearSystem (Fin 2) 1 :=
  ⟨fun i _ => if i=0 then 1 else -1,fun i => if i=0 then 0 else -1⟩
def compatibleBounds : RationalLinearSystem (Fin 2) 1 :=
  ⟨fun i _ => if i=0 then 1 else -1,fun i => if i=0 then 2 else -1⟩
def triangleBounds : RationalLinearSystem (Fin 3) 2 :=
  ⟨fun i j => if i=0 then 1 else if i=1 then (if j=0 then -1 else 0) else
    (if j=0 then 0 else -1),fun i => if i=0 then 3 else -1⟩
def noBounds : RationalLinearSystem (Fin 0) 2 := ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩

#guard rationalLPSolve 0 infeasibleConstant = none
#guard rationalLPSolve 1 conflictingBounds = none
#guard (rationalLPSolve 1 compatibleBounds).map (fun q => q 0) = some 1
#guard (rationalLPSolve 2 triangleBounds).map (fun q => (q 0,q 1)) = some (1,1)
#guard (rationalLPSolve 2 noBounds).map (fun q => (q 0,q 1)) = some (0,0)
end SparseCompletion
