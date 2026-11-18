module

public import BoundedEdgeRegularSubgraphs.SequentialDegreeAtoms
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
# The uniform degree-atom upper bound

Sequential exposure gives a factorial denominator, which is converted
to the scale used in Proposition 8.1.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem card_forward_succ {n : ℕ} (i : Fin n) :
    Fintype.card (ForwardVertex i) + 1 = n - i.val := by
  classical
  unfold ForwardVertex
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter fun j : Fin n ↦ i < j) = Finset.Ioi i := by
    ext j
    simp
  rw [heq, Fin.card_Ioi]
  have hi : i.val < n := i.isLt
  omega

private theorem prod_forward_factorial (n : ℕ) :
    (∏ i : Fin n, ((Fintype.card (ForwardVertex i) : ℝ) + 1)) = (n.factorial : ℝ) := by
  have h : (∏ i : Fin n, (Fintype.card (ForwardVertex i) + 1)) = n.factorial := by
    simp_rw [card_forward_succ]
    calc
      _ = ∏ i : Fin n, ((Fin.revPerm i).val + 1) := by
        apply Finset.prod_congr rfl
        intro i _
        change n - i.val = i.rev.val + 1
        rw [Fin.val_rev]
        have hi : i.val < n := i.isLt
        omega
      _ = ∏ i : Fin n, (i.val + 1) := Equiv.prod_comp (Fin.revPerm (n := n)) (fun i : Fin n ↦ i.val + 1)
      _ = _ := by
        rw [Nat.factorial_eq_prod_range_add_one]
        exact Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) n
  exact_mod_cast h

private theorem sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hx _), ih, pow_succ]

/-- A uniform bound for every degree vector in a bounded independent-edge array. -/
theorem probability_degreeAtom_le_pow_inv_sqrt (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n → ∀ (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ d : Fin n → ℤ,
      (graphLaw p).real (degreeAtom Finset.univ d) ≤ (C / Real.sqrt n) ^ n := by
  obtain ⟨C, hC, hrow⟩ := probability_degreeAtom_le_row_product ξ hξ hξ'
  refine ⟨C * Real.sqrt (Real.exp 1), by positivity, ?_⟩
  intro n hn p hp d
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 < (n : ℝ) / Real.exp 1 := by positivity
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).2
    have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h : 1 ≤ Real.pi * (n : ℝ) := by
      simpa using mul_le_mul hπ hn' (by norm_num : (0 : ℝ) ≤ 1) (Real.pi_pos.le)
    nlinarith
  have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    exact (le_mul_of_one_le_left (pow_nonneg hb.le _) hs).trans (Stirling.le_factorial_stirling n)
  have hden : (Real.sqrt ((n : ℝ) / Real.exp 1)) ^ n ≤ Real.sqrt (n.factorial : ℝ) := by
    rw [← sqrt_nat_pow hb.le]
    exact Real.sqrt_le_sqrt hfac
  calc
    _ ≤ ∏ i : Fin n, C / Real.sqrt ((Fintype.card (ForwardVertex i) : ℝ) + 1) := hrow n p hp d
    _ = C ^ n / Real.sqrt (n.factorial : ℝ) := by
      rw [Finset.prod_div_distrib, ← Real.sqrt_prod Finset.univ (fun _ _ ↦ by positivity),
        prod_forward_factorial, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ C ^ n / (Real.sqrt ((n : ℝ) / Real.exp 1)) ^ n := by
      exact div_le_div_of_nonneg_left (pow_nonneg hC.le _) (by positivity) hden
    _ = _ := by
      rw [← div_pow, Real.sqrt_div (Nat.cast_nonneg n), div_div_eq_mul_div]

end BoundedEdgeRegularSubgraphs
