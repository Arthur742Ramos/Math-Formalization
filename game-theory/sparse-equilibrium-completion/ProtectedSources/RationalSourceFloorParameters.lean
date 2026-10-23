/- AI-assisted formalization under the repository Apache-2.0 license.
Allocation mesh with literal k denominator on the positive-k branch. -/
module
public import ProtectedSources.RationalFloorAccuracyParameters
@[expose] public section
namespace SparseCompletion

def rationalSourceFloorAllocationStep (M ε : ℚ) (k : ℕ) : ℚ :=
  if k=0 then rationalFloorAllocationStep M ε k
  else ε/(((6 : ℕ) : ℚ)*M*(k : ℚ))

theorem rational_source_floor_step_exact (M ε : ℚ) (k : ℕ) (hk : 0 < k) :
    rationalSourceFloorAllocationStep M ε k=ε/(((6 : ℕ) : ℚ)*M*(k : ℚ)) := by
  simp only [rationalSourceFloorAllocationStep,ite_eq_right (Nat.ne_of_gt hk)]

theorem rational_source_floor_step_positive (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) : 0 < rationalSourceFloorAllocationStep M ε k := by
  by_cases hk : k=0
  · simpa only [rationalSourceFloorAllocationStep,ite_eq_left hk] using
      rational_floor_allocation_step_positive M ε k hM hε
  · rw [rationalSourceFloorAllocationStep,ite_eq_right hk]
    have hkQ : 0 < (k : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity

theorem rational_source_floor_error_budget (M ε : ℚ) (k : ℕ)
    (hM : 0 < M) (hε : 0 < ε) :
    ((2 : ℕ) : ℚ)*M*k*rationalSourceFloorAllocationStep M ε k+
      ε/((3 : ℕ) : ℚ)+ε/((3 : ℕ) : ℚ) ≤ ε := by
  have henergy : ((2 : ℕ) : ℚ)*M*k*rationalSourceFloorAllocationStep M ε k ≤
      ε/((3 : ℕ) : ℚ) := by
    by_cases hk : k=0
    · subst k
      simp only [Nat.cast_zero,mul_zero,zero_mul]
      positivity
    · have hkQ : 0 < (k : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have he : ((2 : ℕ) : ℚ)*M*k*rationalSourceFloorAllocationStep M ε k=
          ε/((3 : ℕ) : ℚ) := by
        rw [rationalSourceFloorAllocationStep,ite_eq_right hk]
        field_simp
        ring
      exact le_of_eq he
  linarith

def rationalSourceFloorApproximation {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if he : 0 < ε then
    rationalFloorSearch (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s hs
      (rationalSourceFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ))
  else none


theorem rational_source_floor_node_count (M ε : ℚ) (k : ℕ) (hk : 0 < k) :
    (rationalAllocationNodes k (rationalSourceFloorAllocationStep M ε k)).length=
      (1+Nat.floor ((((6 : ℕ) : ℚ)*M*(k : ℚ))/ε))^k := by
  have he : 1/rationalSourceFloorAllocationStep M ε k=
      (((6 : ℕ) : ℚ)*M*(k : ℚ))/ε := by
    rw [rational_source_floor_step_exact M ε k hk]
    simp only [one_div_div]
  change (rationalGridTuples k (1+Nat.floor (1/rationalSourceFloorAllocationStep M ε k))).length=_
  rw [rational_grid_tuples_length,he]

end SparseCompletion
