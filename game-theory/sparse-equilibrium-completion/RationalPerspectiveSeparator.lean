/- AI-assisted formalization under the repository Apache-2.0 license.
Explicit rational affine coefficients from an actual violated perspective cut.
The tangent inequality is proved by an exact nonnegative square, without a
separation oracle or polynomial LP algorithm assumption. -/
module
public import RationalPerspectiveViolation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalPerspectiveSeparator {m : ℕ} (M r ε : ℚ) (S : Finset (Fin m))
    (q : Fin m → ℚ) : (Fin m → ℚ) × (Fin m → ℚ) × ℚ :=
  let Q := ∑ i ∈ S, q i
  (fun i => if i ∈ S then ((2 : ℕ) : ℚ)*M*Q-M*r-ε else 0,
   fun i => if i ∈ S then 1 else 0,
   -M*Q^2)

noncomputable section

def perspectiveAffineEval {m : ℕ}
    (a : (Fin m → ℚ) × (Fin m → ℚ) × ℚ) (q H : Fin m → ℝ) : ℝ :=
  (∑ i, (a.1 i : ℝ)*q i)+(∑ i, (a.2.1 i : ℝ)*H i)+(a.2.2 : ℝ)

theorem perspective_separator_evaluation {m : ℕ} (M r ε : ℚ)
    (S : Finset (Fin m)) (q0 : Fin m → ℚ) (q H : Fin m → ℝ) :
    perspectiveAffineEval (rationalPerspectiveSeparator M r ε S q0) q H =
      (((2 : ℕ) : ℝ)*(M : ℝ)*(∑ i ∈ S, (q0 i : ℝ))-(M : ℝ)*(r : ℝ)-(ε : ℝ))*mass S q+
        (∑ i ∈ S, H i)-(M : ℝ)*(∑ i ∈ S, (q0 i : ℝ))^2 := by
  classical
  let a : ℚ := ((2 : ℕ) : ℚ)*M*(∑ i ∈ S, q0 i)-M*r-ε
  have hq : (∑ i, ((rationalPerspectiveSeparator M r ε S q0).1 i : ℝ)*q i) =
      (a : ℝ)*mass S q := by
    change (∑ i, ((if i ∈ S then a else 0 : ℚ) : ℝ)*q i) = _
    calc
      _ = ∑ i, if i ∈ S then (a : ℝ)*q i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = mass S (fun i => (a : ℝ)*q i) := masked_sum S _
      _ = (a : ℝ)*mass S q := by simp only [mass,Finset.mul_sum]
  have hH : (∑ i, ((rationalPerspectiveSeparator M r ε S q0).2.1 i : ℝ)*H i) =
      ∑ i ∈ S, H i := by
    change (∑ i, ((if i ∈ S then 1 else 0 : ℚ) : ℝ)*H i) = _
    calc
      _ = ∑ i, if i ∈ S then H i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := masked_sum S H
  unfold perspectiveAffineEval
  rw [hq,hH]
  change (a : ℝ)*mass S q+(∑ i ∈ S, H i)+((-M*(∑ i ∈ S, q0 i)^2 : ℚ) : ℝ) = _
  dsimp only [a]
  push_cast
  ring

theorem perspective_separator_square_gap {m : ℕ} (M r ε : ℚ)
    (S : Finset (Fin m)) (q0 : Fin m → ℚ) (q H : Fin m → ℝ) :
    (M : ℝ)*(mass S q)^2-(M : ℝ)*(r : ℝ)*mass S q+
      (∑ i ∈ S, (H i-(ε : ℝ)*q i))-
      perspectiveAffineEval (rationalPerspectiveSeparator M r ε S q0) q H =
    (M : ℝ)*(mass S q-(∑ i ∈ S, (q0 i : ℝ)))^2 := by
  rw [perspective_separator_evaluation,Finset.sum_sub_distrib,← Finset.mul_sum]
  unfold mass
  ring

theorem perspective_separator_feasible {m : ℕ} (M r ε : ℚ)
    (S : Finset (Fin m)) (q0 : Fin m → ℚ) (q H : Fin m → ℝ)
    (hM : 0 ≤ M) (hc : perspectiveCuts q H (M : ℝ) (r : ℝ) (ε : ℝ)) :
    perspectiveAffineEval (rationalPerspectiveSeparator M r ε S q0) q H ≤ 0 := by
  have hh := perspective_separator_square_gap M r ε S q0 q H
  have hMr : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hn := mul_nonneg hMr (sq_nonneg (mass S q-(∑ i ∈ S, (q0 i : ℝ))))
  have hcut := hc S
  linarith

theorem rational_perspective_separator_sound {m : ℕ} (M r ε : ℚ)
    (q0 H0 : Fin m → ℚ) (hM : 0 ≤ M) (hz : ∀ i, q0 i=0 → H0 i=0)
    (S : Finset (Fin m)) (ho : (rationalPerspectiveViolation M r ε q0 H0).1 = some S) :
    0 < perspectiveAffineEval (rationalPerspectiveSeparator M r ε S q0)
      (fun i => (q0 i : ℝ)) (fun i => (H0 i : ℝ)) ∧
    ∀ q H : Fin m → ℝ, perspectiveCuts q H (M : ℝ) (r : ℝ) (ε : ℝ) →
      perspectiveAffineEval (rationalPerspectiveSeparator M r ε S q0) q H ≤ 0 := by
  constructor
  · have hh := perspective_separator_square_gap M r ε S q0
      (fun i => (q0 i : ℝ)) (fun i => (H0 i : ℝ))
    have hb := rational_perspective_violation_some_sound M r ε q0 H0 hz S ho
    dsimp only [mass] at hb
    simp only [mass,sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero] at hh
    linarith
  · intro q H hc
    exact perspective_separator_feasible M r ε S q0 q H hM hc

end
end SparseCompletion
