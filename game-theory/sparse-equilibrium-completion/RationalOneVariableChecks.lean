/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalOneVariableFinite
public meta import RationalOneVariableFinite
public meta import RationalOneVariable
public import RationalOneVariableFintype
public meta import RationalOneVariableFintype
@[expose] public section
open SparseCompletion.RationalElimination
#guard solve [] = some 0
#guard solve [⟨0,0,0⟩] = some 0
#guard solve [⟨0,1,0⟩] = none
#guard solve [⟨1,0,-3⟩] = some (-3)
#guard solve [⟨-1,0,-2⟩] = some 2
#guard solve [⟨-1,0,-2⟩,⟨1,0,3⟩] = some 2
#guard solve [⟨-1,0,-2⟩,⟨1,0,1⟩] = none
#guard solve [⟨-2,1,-3⟩,⟨3,1,10⟩] = some 2
#guard solveFinite (fun _ : Fin 0 => 0) (fun _ => 0) (fun _ => 0) = some 0
#guard solveFinite (fun _ : Fin 1 => 0) (fun _ => 1) (fun _ => 0) = none

#guard solveFintype (fun _ : Fin 0 => 0) (fun _ => 0) (fun _ => 0) = some 0
#guard solveFintype (fun _ : Unit => 0) (fun _ => 0) (fun _ => 0) = some 0
#guard solveFintype (fun _ : Unit => 0) (fun _ => 1) (fun _ => 0) = none
#guard solveFintype (fun _ : Unit => 1) (fun _ => 0) (fun _ => -3) = some (-3)
#guard solveFintype (fun _ : Unit => -1) (fun _ => 0) (fun _ => -2) = some 2
#guard solveFintype (fun i : Bool => if i then 1 else -1) (fun _ => 0)
  (fun i => if i then 3 else -2) = some 2
#guard solveFintype (fun i : Bool => if i then 1 else -1) (fun _ => 0)
  (fun i => if i then 1 else -2) = none
