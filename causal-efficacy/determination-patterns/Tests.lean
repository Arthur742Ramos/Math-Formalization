module
import DeterminationPatterns

namespace DeterminationPatterns.Regression

def carrier : Region Bool := fun _ => True
def dependency (y x : Bool) : Prop := y ≠ x
def copyOther (x : Bool) (S : Region Bool) : Prop := S (!x)
def off : Region Bool := fun _ => False
def on : Region Bool := fun _ => True
def mixed : Region Bool := fun x => x = true

theorem zero_is_fixed : Fixed (Step carrier dependency copyOther off) off := by
  funext x
  apply propext
  cases x <;> simp [Step, carrier, dependency, copyOther, off, Parents]

theorem one_is_fixed : Fixed (Step carrier dependency copyOther off) on := by
  funext x
  apply propext
  cases x <;> simp [Step, carrier, dependency, copyOther, off, on, Parents]

theorem mixed_is_not_fixed : ¬ Fixed (Step carrier dependency copyOther off) mixed := by
  intro fixed
  have h := congrFun fixed false
  simp [Step, carrier, dependency, copyOther, off, mixed, Parents] at h


/-- Edges ending outside the carrier must not impose the single-parent
assumption on a non-carrier target. -/
inductive BoundaryNode where
  | p | q | outside
  deriving DecidableEq

def boundaryCarrier (x : BoundaryNode) : Prop := x ≠ .outside
def boundaryDependency (_ x : BoundaryNode) : Prop := x = .outside

theorem single_parent_ignores_outside_targets : SingleParent boundaryCarrier boundaryDependency := by
  intro x hc y z hy _
  exact False.elim (hc hy.2)

theorem outside_target_really_has_two_parents :
    Parents boundaryCarrier boundaryDependency .outside .p ∧
    Parents boundaryCarrier boundaryDependency .outside .q ∧
    BoundaryNode.p ≠ BoundaryNode.q := by
  simp [Parents, boundaryCarrier, boundaryDependency]

end DeterminationPatterns.Regression
