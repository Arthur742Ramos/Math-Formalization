module

public import DualityOrthogonality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {G Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] [Nonempty Y]
  {q : ℕ} [NeZero q]

theorem coset_sum (H : AddSubgroup G) (z : G) (f : G → ℝ) :
    (∑ x ∈ univ.filter (fun x => x-z ∈ H), f x) = ∑ h : H, f (z+h) := by
  classical
  rw [sum_filter,← Equiv.sum_comp (Equiv.addLeft z) (fun x => if x-z ∈ H then f x else 0)]
  change (∑ h : G, if z+h-z ∈ H then f (z+h) else 0) = _
  simp only [add_sub_cancel_left]
  rw [← sum_filter]
  exact sum_subtype _ (fun _ => by simp) (fun h => f (z+h))

theorem large_trace_fiber (f : Law G) (T : Y → G →+ ZMod q) (H : AddSubgroup G) (z : G)
    (P δ : ℝ) (hP : 0 < P) (hd : 0 < δ)
    (size : (Fintype.card H : ℝ) * normSq f ≤ P)
    (mass : 1/P ≤ ∑ h : H, f (z+h))
    (support : ∀ x, 0 < f x → δ * Fintype.card Y ≤ (spectrum T x).re) :
    ∃ i : Y, δ^2 * Fintype.card Y ≤
      P^3 * ((univ.filter fun j => trace T H i = trace T H j).card : ℝ) := by
  classical
  let b : ℝ := Fintype.card Y
  let count := fun i => ((univ.filter fun j => trace T H i = trace T H j).card : ℝ)
  obtain ⟨i,_,hmax⟩ := exists_max_image (univ : Finset Y) count univ_nonempty
  refine ⟨i,?_⟩
  change δ^2*b ≤ P^3*count i
  have bp : 0 < b := by dsimp [b]; exact_mod_cast Fintype.card_pos
  have ci : 0 ≤ count i := by dsimp [count]; positivity
  have col : (∑ j, count j) ≤ b*count i := by
    simpa [b] using sum_le_sum (s := (univ : Finset Y)) (fun j _ => hmax j (mem_univ j))
  have spec := (coset_spectrum_bound T H z).trans (mul_le_mul_of_nonneg_left col (Nat.cast_nonneg _))
  have localEnergy : (∑ h : H, f (z+h)^2) ≤ normSq f := by
    rw [← coset_sum H z (fun x => f x^2)]
    exact sum_le_univ_sum_of_nonneg fun x => sq_nonneg _
  have prodBound := (sum_mul_sq_le_sq_mul_sq (univ : Finset H) (fun h => f (z+h))
    (fun h => ‖spectrum T (z+h)‖)).trans (mul_le_mul localEnergy spec
      (sum_nonneg fun _ _ => sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))
  have lower : 1/P*(δ*b) ≤ ∑ h : H, f (z+h)*‖spectrum T (z+h)‖ := by
    apply le_trans (mul_le_mul_of_nonneg_right mass (mul_nonneg hd.le bp.le))
    rw [sum_mul]
    apply sum_le_sum
    intro h _
    rcases (f.nonneg (z+h)).eq_or_lt with hz | hz
    · simp [← hz]
    · exact mul_le_mul_of_nonneg_left ((support _ hz).trans (Complex.re_le_norm _)) (f.nonneg _)
  have lhs := (sq_le_sq₀ (by positivity) (sum_nonneg fun _ _ => mul_nonneg (f.nonneg _) (norm_nonneg _))).mpr lower
  have rhs : normSq f * ((Fintype.card H : ℝ)*(b*count i)) ≤ P*(b*count i) := by
    rw [← mul_assoc,mul_comm (normSq f)]
    exact mul_le_mul_of_nonneg_right size (mul_nonneg bp.le ci)
  have chain := (lhs.trans prodBound).trans rhs
  field_simp [hP.ne'] at chain
  apply le_of_mul_le_mul_left (a := b) _ bp
  nlinarith

end InducedDegreeRepetition.Duality
