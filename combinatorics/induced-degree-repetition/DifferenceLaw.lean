module

public import DualityEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition
namespace Duality.Law

open Finset
open scoped Classical
variable {G H : Type*} [Fintype G] [Fintype H]

theorem ext_law {f g : Law G} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr 1
  exact funext h

/-- Push a finite probability through a map, adding the weights in each fiber. -/
@[expose] noncomputable def push (f : Law G) (p : G → H) : Law H where
  val z := ∑ x ∈ univ.filter (fun x => p x = z), f x
  nonneg _ := sum_nonneg fun _ _ => f.nonneg _
  total := (sum_fiberwise univ p f.val).trans f.total

theorem push_test (f : Law G) (p : G → H) (v : H → ℝ) :
    ∑ z, push f p z*v z = ∑ x, f x*v (p x) := by
  classical
  rw [← sum_fiberwise univ p (fun x => f x*v (p x))]
  apply sum_congr rfl
  intro z _
  change (∑ x ∈ _, f x)*v z = _
  rw [sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [(mem_filter.mp hx).2]

variable [AddCommGroup G] [AddCommGroup H]

@[expose] noncomputable def difference (f : Law G) : Law G := ⟨diff f,diff_nonneg f,sum_diff f⟩

/-- Iterated independent differences. At level one the atom at zero is the
collision probability of the original law. -/
@[expose] noncomputable def iter (f : Law G) : ℕ → Law G
  | 0 => f
  | i+1 => (iter f i).difference

theorem iter_zero (f : Law G) (i : ℕ) : f.iter (i+1) 0 = normSq (f.iter i) := by
  simp [iter,difference,diff,normSq,pow_two]

theorem difference_le (f : Law G) (z : G) : f.difference z ≤ normSq f := by
  have e := sum_le_sum (s := (univ : Finset G)) fun x _ =>
    (show 2*(f x*f (x-z)) ≤ f x^2 + f (x-z)^2 by nlinarith [sq_nonneg (f x-f (x-z))])
  rw [← mul_sum,sum_add_distrib] at e
  have perm := (Equiv.subRight z).sum_comp (fun x => f x^2)
  change (∑ x, f (x-z)^2) = _ at perm
  rw [perm] at e
  change ∑ x, f x*f (x-z) ≤ ∑ x, f x^2
  linarith

omit [AddCommGroup G] in
theorem normSq_le_atom_bound (f : Law G) (b : ℝ) (h : ∀ z, f z ≤ b) : normSq f ≤ b := by
  calc
    _ ≤ ∑ z, f z*b := sum_le_sum fun z _ => by simpa [pow_two] using mul_le_mul_of_nonneg_left (h z) (f.nonneg z)
    _ = _ := by rw [← sum_mul,f.total,one_mul]

theorem iter_antitone (f : Law G) (i : ℕ) : normSq (f.iter (i+1)) ≤ normSq (f.iter i) :=
  normSq_le_atom_bound _ _ (fun z => difference_le _ z)

theorem push_difference (f : Law G) (p : G →+ H) :
    (f.difference.push p) = (f.push p).difference := by
  classical
  suffices allTest : ∀ v : H → ℝ, (∑ z, (f.difference.push p) z*v z) = ∑ z, (f.push p).difference z*v z by
    apply ext_law
    intro z
    simpa [mul_ite] using allTest (fun t => if t = z then (1:ℝ) else 0)
  intro v
  rw [push_test]
  change (∑ x, diff f x*(fun x => v (p x)) x) = ∑ z, diff (f.push p) z*v z
  rw [diff_test,diff_test]
  have h (y : H) := push_test f p (fun z => v (y-z))
  simp_rw [h]
  rw [push_test]
  simp only [map_sub]

theorem push_iter (f : Law G) (p : G →+ H) (i : ℕ) :
    (f.iter i).push p = (f.push p).iter i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iter,iter,push_difference,ih]

end Duality.Law
end InducedDegreeRepetition
