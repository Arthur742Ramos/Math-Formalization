/- AI-assisted formalization under the repository Apache-2.0 license.
Candidate-dependent effective-score sorting for raw perspective moments.
The zero-mass moment condition is explicit; other linear/row guards remain separate. -/
module
public import RationalSortedCutCheck
public import IntervalConic
@[expose] public section
namespace SparseCompletion

def rationalEffectiveScore {m : ℕ} (q H : Fin m → ℚ) (i : Fin m) : ℚ :=
  if q i = 0 then 0 else H i / q i

theorem rational_effective_score_product {m : ℕ} (q H : Fin m → ℚ)
    (hzero : ∀ i, q i = 0 → H i = 0) (i : Fin m) :
    q i * rationalEffectiveScore q H i = H i := by
  unfold rationalEffectiveScore
  split_ifs with h
  · rw [hzero i h, mul_zero]
  · field_simp

def rationalPerspectiveCutCheck {m : ℕ} (M r ε : ℚ) (q H : Fin m → ℚ) : Bool × ℕ :=
  rationalSortedCutCheck M r 0 q (fun i => rationalEffectiveScore q H i-ε)

theorem rational_perspective_cut_check_comparisons {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ) :
    (rationalPerspectiveCutCheck M r ε q H).2 ≤ m*(Nat.log2 m+2)+1 :=
  rational_sorted_cut_check_comparisons _ _ _ _ _

theorem rational_perspective_cut_check_iff {m : ℕ}
    (M r ε : ℚ) (q H : Fin m → ℚ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) (hzero : ∀ i, q i = 0 → H i = 0) :
    (rationalPerspectiveCutCheck M r ε q H).1 = true ↔
      perspectiveCuts (fun i => (q i : ℝ)) (fun i => (H i : ℝ))
        (M : ℝ) (r : ℝ) (ε : ℝ) := by
  have hp : ∀ i, (q i : ℝ)*(rationalEffectiveScore q H i : ℝ) = (H i : ℝ) := by
    intro i
    exact_mod_cast rational_effective_score_product q H hzero i
  have hc := rational_sorted_cut_check_iff M r 0 q
    (fun i => rationalEffectiveScore q H i-ε) hM hq
  have hh : (rationalPerspectiveCutCheck M r ε q H).1 = true ↔
      Cuts (M : ℝ) (r : ℝ) (fun i => (q i : ℝ))
        (fun i => (rationalEffectiveScore q H i : ℝ)-(ε : ℝ)) := by
    simpa only [rationalPerspectiveCutCheck, Cuts, Rat.cast_sub, Rat.cast_zero, sub_nonpos] using hc
  exact hh.trans (perspective_cuts_iff _ _ _ _ _ _ hp)

end SparseCompletion
