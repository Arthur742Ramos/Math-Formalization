/- AI-assisted controls; exact execution status is external. -/
module
import RationalConeEncoding
public meta import RationalConeEncoding
open SparseCompletion

def checkCone (label : String) (p : Prop) [Decidable p] : IO Unit := do
  if decide p then IO.println (label ++ ": PASS")
  else throw (IO.userError (label ++ ": FAIL"))

#eval checkCone "rational coefficient retained"
  ((rationalPrefixConeRows (fun _ : Fin 1 => (1/3 : ℚ)) (2/3) (3/4) (1/5) 0).u 0=11/20)
#eval checkCone "boundary row accepted"
  ((rationalPrefixConeRows (fun _ : Fin 1 => (0 : ℚ)) 1 1 0 0).RationalSatisfied
    (fun _ => 1))
#eval checkCone "violating row rejected"
  (¬ (rationalPrefixConeRows (fun _ : Fin 1 => (0 : ℚ)) 1 1 0 0).RationalSatisfied
    (fun _ => 2))
#eval checkCone "negative score accepted"
  ((rationalPrefixConeRows (fun _ : Fin 1 => (-1 : ℚ)) 1 1 0 0).RationalSatisfied
    (fun _ => 1))
#eval checkCone "second prefix contains both labels"
  ((rationalPrefixConeRows (fun _ : Fin 2 => (0 : ℚ)) 1 1 0 1).w 0=1 ∧
   (rationalPrefixConeRows (fun _ : Fin 2 => (0 : ℚ)) 1 1 0 1).w 1=1)
#eval checkCone "empty system has zero coordinate slots"
  (rationalConeSystemCoordinateCount 0 0=0)
