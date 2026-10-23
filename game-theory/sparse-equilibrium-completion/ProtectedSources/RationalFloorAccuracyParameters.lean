/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorSearch
@[expose] public section
namespace SparseCompletion

def rationalFloorAllocationStep (M ε : ℚ) (k : ℕ) : ℚ := ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1))

theorem rational_third_positive (ε : ℚ) (hε : 0 < ε) : 0 < ε/((3 : ℕ) : ℚ) :=
  div_pos hε (by norm_num)

theorem rational_floor_allocation_step_positive (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) : 0 < rationalFloorAllocationStep M ε k := by
  unfold rationalFloorAllocationStep
  positivity

theorem rational_floor_allocation_error_budget (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) :
    ((2 : ℕ) : ℚ)*M*k*rationalFloorAllocationStep M ε k+ε/((3 : ℕ) : ℚ)+ε/((3 : ℕ) : ℚ) ≤ ε := by
  have hd : 0 < ((6 : ℕ) : ℚ)*M*((k : ℚ)+1) := by positivity
  have hs : ((2 : ℕ) : ℚ)*M*k*(ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1))) ≤ ε/((3 : ℕ) : ℚ) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_pos hε hM]
  change ((2 : ℕ) : ℚ)*M*k*(ε/(((6 : ℕ) : ℚ)*M*((k : ℚ)+1)))+ε/((3 : ℕ) : ℚ)+ε/((3 : ℕ) : ℚ) ≤ ε
  linarith

def RationalIntervalParameters.withSlack {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (η : ℚ) (hη : 0 < η) :
    RationalIntervalParameters k m I := {d with η := η, positiveSlack := hη}

def rationalFloorApproximation {k m : ℕ} (d : RationalIntervalParameters k m (Fin m))
    (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if he : 0 < ε then
    rationalFloorSearch (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s hs
      (rationalFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ))
  else none

end SparseCompletion
