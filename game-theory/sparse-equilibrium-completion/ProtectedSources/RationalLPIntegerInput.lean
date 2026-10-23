/- AI-assisted formalization under repository Apache-2.0.
Global denominator clearing for the literal augmented LP
input matrix, using David Loeffler's pinned Matrix.den / Matrix.num API. -/
module
public import ProtectedSources.RationalInputHeight
public import ProtectedSources.RationalLinearSystem
public import Mathlib.LinearAlgebra.Matrix.Integer
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- The RHS occupies column none; every coefficient occupies its original
some j column. Nothing depends on a solver result or on selected active rows. -/
def rationalLPAugmentedMatrix {I : Type*} {n : ℕ} (S : RationalLinearSystem I n) :
    Matrix I (Option (Fin n)) ℚ := fun row col => col.elim (S.rightSide row) (S.coefficient row)

def rationalLPInputDenominator {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) : ℕ := (rationalLPAugmentedMatrix S).den

def rationalLPIntegerInput {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) : Matrix I (Option (Fin n)) ℤ :=
  (rationalLPAugmentedMatrix S).num

def rationalLPIntegerEntryHeight (rows vars B : ℕ) : ℕ := B*(rows*(vars+1)+1)

theorem rational_lp_input_denominator_positive {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) : 0 < rationalLPInputDenominator S :=
  Nat.pos_of_ne_zero (Matrix.den_ne_zero _)

theorem rational_lp_augmented_input_height {I : Type*} {n B : ℕ}
    (S : RationalLinearSystem I n)
    (hc : ∀ row j, RationalInputHeight (S.coefficient row j) B)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) B) :
    ∀ row col, RationalInputHeight (rationalLPAugmentedMatrix S row col) B := by
  intro row col
  cases col with
  | none => exact hr row
  | some j => exact hc row j

theorem rational_lp_input_denominator_bound {I : Type*} [Fintype I] {n B : ℕ}
    (S : RationalLinearSystem I n)
    (hc : ∀ row j, RationalInputHeight (S.coefficient row j) B)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) B) :
    rationalLPInputDenominator S ≤ Nat.pow 2 (B*(Fintype.card I*(n+1))) := by
  classical
  let A := rationalLPAugmentedMatrix S
  let D := ∏ p : I × Option (Fin n), (A p.1 p.2).den
  have hDpos : 0 < D := Finset.prod_pos (fun p _ => (A p.1 p.2).den_pos)
  have hdvd : A.den ∣ D := Matrix.den_dvd_iff.mpr (fun row col =>
    Finset.dvd_prod_of_mem (fun p : I × Option (Fin n) => (A p.1 p.2).den) (Finset.mem_univ (row,col)))
  have hprod : D ≤ (Nat.pow 2 B)^(Fintype.card (I × Option (Fin n))) :=
    Finset.prod_le_pow_card _ _ _ (fun p _ => (rational_lp_augmented_input_height S hc hr p.1 p.2).2)
  have hpow (a t : ℕ) : a^t = Nat.pow a t := by
    induction t with
    | zero => rfl
    | succ t ih => rw [pow_succ, ih]; rfl
  have hb : D ≤ Nat.pow 2 (B*(Fintype.card I*(n+1))) := by
    have hprod' : D ≤ Nat.pow (Nat.pow 2 B) (Fintype.card I*(n+1)) := by
      simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, hpow] using hprod
    exact hprod'.trans_eq (Nat.pow_mul 2 B (Fintype.card I*(n+1))).symm
  exact (Nat.le_of_dvd hDpos hdvd).trans hb

theorem rational_lp_integer_input_cast {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (row : I) (col : Option (Fin n)) :
    (rationalLPIntegerInput S row col : ℚ) =
      (rationalLPInputDenominator S : ℚ)*rationalLPAugmentedMatrix S row col := by
  have he := (div_eq_iff (by exact_mod_cast (ne_of_gt (rational_lp_input_denominator_positive S)) :
      (rationalLPInputDenominator S : ℚ) ≠ 0)).mp
    ((rationalLPAugmentedMatrix S).num_div_den row col)
  simpa only [rationalLPIntegerInput, rationalLPInputDenominator, mul_comm] using he

theorem rational_lp_integer_input_real_cast {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) (row : I) (col : Option (Fin n)) :
    (rationalLPIntegerInput S row col : ℝ) =
      (rationalLPInputDenominator S : ℝ)*(rationalLPAugmentedMatrix S row col : ℝ) := by
  exact_mod_cast rational_lp_integer_input_cast S row col

theorem rational_lp_integer_input_entry_bound {I : Type*} [Fintype I] {n B : ℕ}
    (S : RationalLinearSystem I n)
    (hc : ∀ row j, RationalInputHeight (S.coefficient row j) B)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) B) (row : I) (col : Option (Fin n)) :
    (rationalLPIntegerInput S row col).natAbs ≤
      Nat.pow 2 (rationalLPIntegerEntryHeight (Fintype.card I) n B) := by
  let z := rationalLPIntegerInput S row col
  have hD := rational_lp_input_denominator_bound S hc hr
  have hA := rational_input_height_magnitude (rational_lp_augmented_input_height S hc hr row col)
  have hz : |(z : ℚ)| ≤
      (Nat.pow 2 (rationalLPIntegerEntryHeight (Fintype.card I) n B) : ℕ) := by
    calc
      _ = (rationalLPInputDenominator S : ℚ)*|rationalLPAugmentedMatrix S row col| := by
        rw [rational_lp_integer_input_cast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ ((Nat.pow 2 (B*(Fintype.card I*(n+1))) : ℕ) : ℚ)*((Nat.pow 2 B : ℕ) : ℚ) :=
        mul_le_mul (by exact_mod_cast hD) hA (abs_nonneg _) (by positivity)
      _ = _ := by
        have hp : Nat.pow 2 (B*(Fintype.card I*(n+1)))*Nat.pow 2 B =
            Nat.pow 2 (B*(Fintype.card I*(n+1))+B) := (Nat.pow_add 2 _ _).symm
        have he : B*(Fintype.card I*(n+1))+B = rationalLPIntegerEntryHeight (Fintype.card I) n B := by
          unfold rationalLPIntegerEntryHeight
          ring
        exact_mod_cast hp.trans (congrArg (Nat.pow 2) he)
  have he : (z.natAbs : ℚ) = |(z : ℚ)| := by
    simpa only [Rat.num_intCast, Rat.den_intCast, Nat.cast_one, mul_one] using
      rational_num_abs_identity (z : ℚ)
  exact_mod_cast he.trans_le hz

end SparseCompletion
