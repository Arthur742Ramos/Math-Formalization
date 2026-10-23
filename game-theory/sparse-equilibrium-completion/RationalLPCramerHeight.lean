/- AI-assisted formalization under repository Apache-2.0.
Elementary integer determinant bounds and canonical rational
Cramer witness heights. These are certificate-size bounds, not bit time. -/
module
public import RationalLPIntegerInput
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.NatAbs
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion

def rationalLPSmallWitnessHeight (rows vars B : ℕ) : ℕ :=
  vars*vars+vars*rationalLPIntegerEntryHeight rows vars B

theorem rational_lp_factorial_binary_bound (n : ℕ) : n.factorial ≤ Nat.pow 2 (n*n) := by
  calc
    _ ≤ n^n := Nat.factorial_le_pow n
    _ ≤ (Nat.pow 2 n)^n := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) n
    _ = _ := (Nat.pow_mul 2 n n).symm

theorem rational_lp_integer_determinant_binary_bound {n E : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ Nat.pow 2 E) :
    A.det.natAbs ≤ Nat.pow 2 (n*n+n*E) := by
  classical
  have hterm (σ : Equiv.Perm (Fin n)) :
      (((Equiv.Perm.sign σ : ℤ)*∏ i, A (σ i) i).natAbs) ≤ (Nat.pow 2 E)^n := by
    rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
    calc
      _ = ∏ i, (A (σ i) i).natAbs := map_prod Int.natAbsHom _ _
      _ ≤ _ := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.prod_le_pow_card (Finset.univ : Finset (Fin n))
            (fun i => (A (σ i) i).natAbs) (Nat.pow 2 E) (fun i _ => hA (σ i) i)
  have hdet : A.det.natAbs ≤ n.factorial*(Nat.pow 2 E)^n := by
    rw [Matrix.det_apply']
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin n),
          (((Equiv.Perm.sign σ : ℤ)*∏ i, A (σ i) i).natAbs) := Int.natAbs_sum_le _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), (Nat.pow 2 E)^n := Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  calc
    _ ≤ n.factorial*(Nat.pow 2 E)^n := hdet
    _ ≤ Nat.pow 2 (n*n)*Nat.pow 2 (E*n) := Nat.mul_le_mul
      (rational_lp_factorial_binary_bound n) (le_of_eq (Nat.pow_mul 2 E n).symm)
    _ = _ := by
      have hp : Nat.pow 2 (n*n)*Nat.pow 2 (E*n) = Nat.pow 2 (n*n+E*n) :=
        (Nat.pow_add 2 _ _).symm
      exact hp.trans (congrArg (Nat.pow 2) (by ring))

/-- Canonical reduction of an integer quotient cannot enlarge either
integer component. This avoids the coarse generic rational-division bound. -/
theorem rational_lp_integer_quotient_input_height {P : ℕ} (a b : ℤ) (hb : b ≠ 0)
    (ha : a.natAbs ≤ Nat.pow 2 P) (hbd : b.natAbs ≤ Nat.pow 2 P) :
    RationalInputHeight ((a : ℚ)/(b : ℚ)) P := by
  let q : ℚ := (a : ℚ)/(b : ℚ)
  obtain ⟨c,hn,hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro hz
    apply hb
    rw [hd, hz, zero_mul]
  have hcn : 1 ≤ c.natAbs := by
    exact Nat.one_le_iff_ne_zero.mpr (fun hz => hc (Int.natAbs_eq_zero.mp hz))
  have hnum : a.natAbs = c.natAbs*q.num.natAbs := by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hn
  have hden : b.natAbs = c.natAbs*q.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd
  constructor
  · have hh : q.num.natAbs ≤ c.natAbs*q.num.natAbs := by
      simpa only [one_mul] using Nat.mul_le_mul_right q.num.natAbs hcn
    exact (hh.trans_eq hnum.symm).trans ha
  · have hh : q.den ≤ c.natAbs*q.den := by
      simpa only [one_mul] using Nat.mul_le_mul_right q.den hcn
    exact (hh.trans_eq hden.symm).trans hbd

def rationalIntegerCramerWitness {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) :
    Fin n → ℚ := fun j => ((A.updateCol j b).det : ℚ)/(A.det : ℚ)

theorem rational_integer_cramer_witness_input_height {n E : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (hdet : A.det ≠ 0)
    (hA : ∀ i j, (A i j).natAbs ≤ Nat.pow 2 E)
    (hb : ∀ i, (b i).natAbs ≤ Nat.pow 2 E) :
    ∀ j, RationalInputHeight (rationalIntegerCramerWitness A b j) (n*n+n*E) := by
  intro j
  apply rational_lp_integer_quotient_input_height _ _ hdet
  · apply rational_lp_integer_determinant_binary_bound
    intro i k
    rw [Matrix.updateCol_apply]
    split
    · exact hb i
    · exact hA i k
  · exact rational_lp_integer_determinant_binary_bound A hA

/-- This is an equality with the original real point, obtained from the
actual integer Cramer quotients and the actual active square equations. -/
theorem rational_integer_cramer_witness_real_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (hdet : A.det ≠ 0)
    (x : Fin n → ℝ)
    (hx : (fun i j => (A i j : ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x = fun i => (b i : ℝ)) :
    (fun j => (rationalIntegerCramerWitness A b j : ℝ)) = x := by
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j : ℝ)
  let d : Fin n → ℝ := fun i => (b i : ℝ)
  have hx' : C *ᵥ x = d := hx
  have hc : Matrix.cramer C d = C.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hx', Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext j
  have hm : (A.updateCol j b).map (fun z : ℤ => (z : ℝ)) =
      C.updateCol j d := by
    exact Matrix.map_updateCol (M := A) (j := j) (c := b) (fun z : ℤ => (z : ℝ))
  have hcastj : ((A.updateCol j b).det : ℝ) = (C.updateCol j d).det :=
    (Int.cast_det (A.updateCol j b)).trans (congrArg Matrix.det hm)
  have hcastA : (A.det : ℝ) = C.det := Int.cast_det A
  have he : ((A.updateCol j b).det : ℝ) = (A.det : ℝ)*x j := by
    calc
      _ = (C.updateCol j d).det := hcastj
      _ = Matrix.cramer C d j := (Matrix.cramer_apply (A := C) (b := d) j).symm
      _ = C.det*x j := by simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hc j
      _ = _ := congrArg (fun c : ℝ => c*x j) hcastA.symm
  simp only [rationalIntegerCramerWitness, Rat.cast_div, Rat.cast_intCast]
  apply (div_eq_iff (by exact_mod_cast hdet : (A.det : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using he

end SparseCompletion
