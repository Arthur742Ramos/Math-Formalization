/- AI-assisted formalization under the repository Apache-2.0 license.
Actual interval-candidate cut output. Linear/core/global guards remain separate;
a missing cut alone is not a valid complete candidate. -/
module
public import RationalPerspectiveViolation
public import RationalIntervalCutCheck
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalViolation {k m : ℕ} (M r ε : ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (V : Fin m → Fin k → ℚ) :
    Option (Finset (Fin m)) × ℕ :=
  rationalPerspectiveViolation M r ε q (fun i => ∑ a, p a*V i a)

theorem rational_interval_violation_none_iff_check {k m : ℕ} (M r ε : ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (V : Fin m → Fin k → ℚ) :
    (rationalIntervalViolation M r ε p q V).1 = none ↔
      (rationalIntervalCutCheck M r ε p q V).1 = true :=
  rational_perspective_violation_none_iff_check _ _ _ _ _

theorem rational_interval_violation_none_iff_cuts {k m : ℕ} (M r ε : ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i)
    (hb : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    (rationalIntervalViolation M r ε p q V).1 = none ↔
      perspectiveCuts (fun i => (q i : ℝ))
        (intervalMomentScore (fun a => (p a : ℝ)) (fun i a => (V i a : ℝ)))
        (M : ℝ) (r : ℝ) (ε : ℝ) :=
  (rational_interval_violation_none_iff_check M r ε p q V).trans
    (rational_interval_cut_check_iff M r ε lo hi V p q hM hq hb)

theorem rational_interval_violation_some_sound {k m : ℕ} (M r ε : ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hb : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i)
    (S : Finset (Fin m)) (ho : (rationalIntervalViolation M r ε p q V).1 = some S) :
    0 < (M : ℝ)*(mass S (fun i => (q i : ℝ)))^2-
      (M : ℝ)*(r : ℝ)*mass S (fun i => (q i : ℝ))+
      (∑ i ∈ S, (intervalMomentScore (fun a => (p a : ℝ))
        (fun i a => (V i a : ℝ)) i-(ε : ℝ)*(q i : ℝ))) := by
  have hh := rational_perspective_violation_some_sound M r ε q
    (fun i => ∑ a, p a*V i a) (rational_perspective_moment_zero lo hi V p q hb) S ho
  simpa only [Rat.cast_sum,Rat.cast_mul,intervalMomentScore] using hh

theorem rational_interval_violation_comparisons {k m : ℕ} (M r ε : ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (V : Fin m → Fin k → ℚ) :
    (rationalIntervalViolation M r ε p q V).2 ≤ m*(Nat.log2 m+2)+1 :=
  rational_perspective_violation_comparisons _ _ _ _ _

end SparseCompletion
