module
/- Exceptional profile: literal inverse-minor multipliers establish its
   complete affine-line solution set, without trusting Gaussian elimination. -/
public import F3Linear
public import ArithmeticCertificate
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace CoveringExceptional
open CoveringF3 CoveringFormalRound3Linear

@[expose] def exceptional : LinearWitness := ⟨12, [1, 1, 0, 2, 2, 0, 2, 0, 1, 0], []⟩
@[expose] def matrix3 (r c : Nat) : F3 := ofNat (coefficient exceptional r c)
@[expose] def right3 (r : Nat) : F3 := ofNat (rhs exceptional r)
@[expose] def particular : List Nat := [1, 2, 2, 1, 1, 1, 1, 0, 0, 0]
@[expose] def direction : List Nat := [1, 1, 2, 2, 1, 0, 0, 0, 1, 1]
@[expose] def leftMultipliers : List (List Nat) := [[0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0], [0, 2, 0, 2, 2, 0, 2, 1, 0, 1, 1, 0, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0], [0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
@[expose] def point (c : Nat) : F3 := ofNat (particular.getD c 0)
@[expose] def dir (c : Nat) : F3 := ofNat (direction.getD c 0)
@[expose] def multiplier (j r : Nat) : F3 := ofNat ((leftMultipliers.getD j []).getD r 0)

theorem inverse_minor_certificate : ∀ j : Fin 9,
    (∀ c : Fin 10, CoveringF3.sum 15 (fun r => mul (multiplier j.val r) (matrix3 r c.val)) =
      affineRow j.val 9 (dir j.val) c.val) ∧
    CoveringF3.sum 15 (fun r => mul (multiplier j.val r) (right3 r)) = point j.val := by decide

/-- Every solution is on the stated affine line; no rank or search result is assumed. -/
theorem affine_line (v : Nat → F3)
    (hv : ∀ r, r < 15 → CoveringF3.sum 10 (fun c => mul (matrix3 r c) (v c)) = right3 r) :
    ∀ j, j < 10 → v j = add (point j) (mul (dir j) (v 9)) := by
  intro j hj
  by_cases hfree : j = 9
  · subst j
    simp only [point, dir, particular, direction, List.getD]
    change v 9 = add 0 (mul 1 (v 9))
    rw [mul_one, zero_add]
  · have hj9 : j < 9 := by omega
    obtain ⟨hA, hb⟩ := inverse_minor_certificate ⟨j,hj9⟩
    have hc := certified_consequence 15 10 matrix3 right3 (multiplier j)
      (affineRow j 9 (dir j)) v (point j) (fun c hc => hA ⟨c,hc⟩) hb hv
    rw [sum_affine_row 10 j 9 hj (by decide)] at hc
    exact recover_affine (v j) (point j) (dir j) (v 9) hc

theorem affine_line_is_solution : ∀ t : F3, ∀ r : Fin 15,
    CoveringF3.sum 10 (fun c => mul (matrix3 r.val c) (add (point c) (mul (dir c) t))) = right3 r.val := by decide

/-- The specified three-entry fibre has equal upper differences, so its
    sum of squares is zero for every parameter, contrary to the required two. -/
theorem affine_quadratic_failure : ∀ t : F3,
    add (mul (add 1 t) (add 1 t))
      (add (mul (add 1 t) (add 1 t)) (mul (add 1 t) (add 1 t))) ≠ 2 := by decide

@[expose] def upperDifference (v : Nat → F3) (r j : Nat) : F3 :=
  add (v r) (neg (ofNat (entry 12 r j / 3 +
    if exceptional.low.getD r 0 < entry 12 r j % 3 then 1 else 0)))

@[expose] def quadratic (v : Nat → F3) : F3 :=
  add (mul (upperDifference v 0 2) (upperDifference v 0 2))
    (add (mul (upperDifference v 8 2) (upperDifference v 8 2))
      (mul (upperDifference v 9 2) (upperDifference v 9 2)))

theorem quadratic_failure_in_original_fibre : ∀ t : F3,
    quadratic (fun c => add (point c) (mul (dir c) t)) ≠ 2 := by decide

/-- No upper-digit assignment satisfies both the complete linear system
    and the required second moment of the exceptional fibre. -/
theorem no_fibre_solution (v : Nat → F3)
    (hv : ∀ r, r < 15 → CoveringF3.sum 10 (fun c => mul (matrix3 r c) (v c)) = right3 r)
    (hq : quadratic v = 2) : False := by
  have ha := affine_line v hv
  have h0 := ha 0 (by decide)
  have h8 := ha 8 (by decide)
  have h9 := ha 9 (by decide)
  apply quadratic_failure_in_original_fibre (v 9)
  have heq : quadratic v = quadratic (fun c => add (point c) (mul (dir c) (v 9))) := by
    unfold quadratic upperDifference
    rw [h0, h8]
    simp only [show point 9 = 0 by decide, show dir 9 = 1 by decide, mul_one, zero_add]
  exact heq.symm.trans hq

#print axioms inverse_minor_certificate
#print axioms no_fibre_solution
#print axioms affine_line
#print axioms affine_line_is_solution
#print axioms affine_quadratic_failure
end CoveringExceptional
