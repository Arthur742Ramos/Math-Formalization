/- AI-assisted formalization under the repository Apache-2.0 license.
The cut component of candidate separation, with effective moments formed from
the actual perspective variables. Other linear and zero-row guards are separate. -/
module
public import RationalPerspectiveCutCheck
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_perspective_moment_zero {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hb : ∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) :
    ∀ i, q i = 0 → (∑ h, p h*V i h) = 0 := by
  intro i hiq
  apply Finset.sum_eq_zero
  intro h _
  have hv : V i h = 0 := by
    have hh := hb i h
    have hl := hh.1
    have hu := hh.2
    rw [hiq, mul_zero] at hl hu
    exact le_antisymm hu hl
  rw [hv, mul_zero]

def rationalIntervalCutCheck {k m : ℕ} (M r ε : ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (V : Fin m → Fin k → ℚ) : Bool × ℕ :=
  rationalPerspectiveCutCheck M r ε q (fun i => ∑ h, p h*V i h)

theorem rational_interval_cut_check_comparisons {k m : ℕ} (M r ε : ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (V : Fin m → Fin k → ℚ) :
    (rationalIntervalCutCheck M r ε p q V).2 ≤ m*(Nat.log2 m+2)+1 :=
  rational_perspective_cut_check_comparisons _ _ _ _ _

theorem rational_interval_cut_check_iff {k m : ℕ}
    (M r ε : ℚ) (lo hi V : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i)
    (hb : ∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) :
    (rationalIntervalCutCheck M r ε p q V).1 = true ↔
      perspectiveCuts (fun i => (q i : ℝ))
        (intervalMomentScore (fun h => (p h : ℝ)) (fun i h => (V i h : ℝ)))
        (M : ℝ) (r : ℝ) (ε : ℝ) := by
  have hh := rational_perspective_cut_check_iff M r ε q
    (fun i => ∑ h, p h*V i h) hM hq
    (rational_perspective_moment_zero lo hi V p q hb)
  change (rationalPerspectiveCutCheck M r ε q (fun i => ∑ h, p h*V i h)).1 = true ↔
    perspectiveCuts (fun i => (q i : ℝ))
      (fun i => ∑ h, (p h : ℝ)*(V i h : ℝ)) (M : ℝ) (r : ℝ) (ε : ℝ)
  simpa only [Rat.cast_sum, Rat.cast_mul] using hh

end SparseCompletion
