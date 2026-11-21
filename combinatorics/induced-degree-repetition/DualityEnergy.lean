module

public import Concentration
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical

/-- A probability with respect to counting measure. -/
structure Law (G : Type*) [Fintype G] where
  val : G → ℝ
  nonneg : ∀ x, 0 ≤ val x
  total : ∑ x, val x = 1

instance {G : Type*} [Fintype G] : CoeFun (Law G) fun _ => G → ℝ := ⟨Law.val⟩

variable {G : Type*} [AddCommGroup G] [Fintype G]

@[expose] def diff (f : G → ℝ) (z : G) : ℝ := ∑ x, f x * f (x-z)

theorem diff_nonneg (f : Law G) (z : G) : 0 ≤ diff f z :=
  sum_nonneg fun x _ => mul_nonneg (f.nonneg x) (f.nonneg _)

theorem sum_diff (f : Law G) : ∑ z, diff f z = 1 := by
  simp only [diff]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have same (x : G) : ∑ z, f (x-z) = 1 := ((Equiv.subLeft x).sum_comp f.val).trans f.total
  simpa only [same,mul_one] using f.total

/-- Self-convolution and convolution with the reflected law have the same squared
two-norm. At fixed x,y the two expansions are related by z ↦ x+y−z. -/
theorem normSq_diff (f : G → ℝ) : normSq (diff f) = normSq (convolution f f) := by
  simp only [normSq, diff, convolution, pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply Fintype.sum_equiv (Equiv.subLeft (x+y))
  intro z
  change _ = f y * f (x+y-z-y) * (f x * f (x+y-z-x))
  rw [show x+y-z-x = y-z by abel,show x+y-z-y = x-z by abel]
  ring

omit [AddCommGroup G] in
theorem normSq_le_one (f : Law G) : normSq f ≤ 1 := by
  rw [← f.total]
  apply sum_le_sum
  intro x hx
  have le : f x ≤ 1 := (single_le_sum (fun i _ => f.nonneg i) (mem_univ x)).trans_eq f.total
  nlinarith [mul_nonneg (f.nonneg x) (sub_nonneg.mpr le)]

omit [AddCommGroup G] in
theorem one_le_card_mul_normSq (f : Law G) : 1 ≤ Fintype.card G * normSq f := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset G) (fun _ => (1:ℝ)) f.val
  simpa [normSq,f.total] using h

/-- Restrict a discrete law to a nonempty-mass event. -/
@[expose] noncomputable def conditioned (f : G → ℝ) (nonneg : ∀ x, 0 ≤ f x) (S : Finset G)
    (pos : 0 < ∑ x ∈ S, f x) : Law G where
  val x := if x ∈ S then f x / (∑ z ∈ S, f z) else 0
  nonneg x := by split <;> positivity [nonneg x]
  total := by simp [← sum_div, pos.ne']

/-- Summing a test over the difference law gives its expectation on an independent
ordered pair. -/
theorem diff_test (f : G → ℝ) (g : G → ℝ) :
    (∑ z, diff f z * g z) = ∑ x, f x * ∑ y, f y * g (x-y) := by
  simp only [diff,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply Fintype.sum_equiv (Equiv.subLeft x)
  intro z
  simp [mul_assoc]

/-- Any heavy set of differences admits a single anchor making its translate heavy
under the preceding law. -/
theorem lift_difference_set (f : Law G) (S : Finset G) :
    ∃ z : G, (∑ x ∈ S, diff f x) ≤ ∑ x ∈ univ.filter (fun x => x-z ∈ S), f x := by
  classical
  let g := fun x : G => if x ∈ S then (1:ℝ) else 0
  let F := fun z => ∑ x ∈ univ.filter (fun x => x-z ∈ S), f x
  have expand : (∑ x ∈ S, diff f x) = ∑ z, f z * F z := by
    calc
      _ = ∑ z, diff f z * g z := by simp [g, mul_ite]
      _ = _ := diff_test f g
      _ = _ := by
        simp only [F,g,sum_filter,mul_sum,mul_ite,mul_one,mul_zero]
        rw [sum_comm]
        apply sum_congr rfl
        intro z _
        apply sum_congr rfl
        intro x _
        split <;> simp_all [mul_comm]
  obtain ⟨z,hz,hm⟩ := exists_max_image (univ : Finset G) F univ_nonempty
  refine ⟨z,expand.le.trans ?_⟩
  calc
    _ ≤ ∑ x, f x * F z := sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hm x (mem_univ x)) (f.nonneg x)
    _ = F z := by rw [← sum_mul,f.total,one_mul]

end InducedDegreeRepetition.Duality
