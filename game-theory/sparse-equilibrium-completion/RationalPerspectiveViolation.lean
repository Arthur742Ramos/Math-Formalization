/- AI-assisted formalization under the repository Apache-2.0 license.
Actual original-label violating cuts for raw perspective moments. Comparison
counts exclude score formation, rational division and payload allocation. -/
module
public import RationalNodupCutPayload
public import RationalPerspectiveCutCheck
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalPerspectiveViolation {m : ℕ} (M r ε : ℚ) (q H : Fin m → ℚ) :
    Option (Finset (Fin m)) × ℕ :=
  rationalNodupSortedViolation M r 0 q (fun i => rationalEffectiveScore q H i-ε)

theorem rational_perspective_violation_none_iff_check {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ) :
    (rationalPerspectiveViolation M r ε q H).1 = none ↔
      (rationalPerspectiveCutCheck M r ε q H).1 = true := by
  unfold rationalPerspectiveViolation rationalPerspectiveCutCheck
  rw [rational_nodup_sorted_violation_eq]
  exact rational_sorted_violation_none_iff_check _ _ _ _ _

theorem rational_perspective_violation_none_iff_cuts {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hz : ∀ i, q i=0 → H i=0) :
    (rationalPerspectiveViolation M r ε q H).1 = none ↔
      perspectiveCuts (fun i => (q i : ℝ)) (fun i => (H i : ℝ))
        (M : ℝ) (r : ℝ) (ε : ℝ) :=
  (rational_perspective_violation_none_iff_check M r ε q H).trans
    (rational_perspective_cut_check_iff M r ε q H hM hq hz)

theorem rational_perspective_violation_some_sound {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ) (hz : ∀ i, q i=0 → H i=0)
    (S : Finset (Fin m)) (hout : (rationalPerspectiveViolation M r ε q H).1 = some S) :
    0 < (M : ℝ)*(mass S (fun i => (q i : ℝ)))^2-
      (M : ℝ)*(r : ℝ)*mass S (fun i => (q i : ℝ))+
      (∑ i ∈ S, ((H i : ℝ)-(ε : ℝ)*(q i : ℝ))) := by
  have hh := rational_nodup_sorted_violation_some_sound M r 0 q
    (fun i => rationalEffectiveScore q H i-ε) S hout
  have he : (∑ i ∈ S, (q i : ℝ)*((rationalEffectiveScore q H i-ε : ℚ) : ℝ)) =
      ∑ i ∈ S, ((H i : ℝ)-(ε : ℝ)*(q i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hp : (q i : ℝ)*(rationalEffectiveScore q H i : ℝ) = (H i : ℝ) := by
      exact_mod_cast rational_effective_score_product q H hz i
    rw [Rat.cast_sub,mul_sub,hp,mul_comm (q i : ℝ) (ε : ℝ)]
  rw [he] at hh
  norm_num only [Rat.cast_zero] at hh
  nlinarith

theorem rational_perspective_violation_comparisons {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ) :
    (rationalPerspectiveViolation M r ε q H).2 ≤ m*(Nat.log2 m+2)+1 :=
  rational_nodup_sorted_violation_comparisons _ _ _ _ _

end SparseCompletion
