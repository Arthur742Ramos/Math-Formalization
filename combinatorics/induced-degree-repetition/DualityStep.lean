module

public import DualitySpectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {G Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] [Nonempty Y]
  {q : ℕ} [NeZero q]

/-- In a biased law the differences with large real character sum carry enough
mass to condition on. The new law is supported on those differences. -/
theorem spectrum_step (f : Law G) (T : Y → G →+ ZMod q) (ε : ℝ) (he : 0 < ε)
    (hb : ε * Fintype.card Y ≤ ‖average f (spectrum T)‖) :
    ∃ f' : Law G, (∀ z, ε^2/2 * f' z ≤ diff f z) ∧
      (∀ z, 0 < f' z → ε^2/2 * Fintype.card Y ≤ (spectrum T z).re) := by
  classical
  let b : ℝ := Fintype.card Y
  let δ := ε^2/2
  let S := univ.filter fun z => δ*b ≤ (spectrum T z).re
  let m := ∑ z ∈ S, diff f z
  have bp : 0 < b := by dsimp [b]; exact_mod_cast Fintype.card_pos
  have dp : 0 < δ := by dsimp [δ]; positivity
  have upper (z : G) : diff f z * (spectrum T z).re ≤
      diff f z * (δ*b) + (if z ∈ S then diff f z * b else 0) := by
    by_cases hz : z ∈ S
    · rw [ite_eq_left hz]
      have u := (Complex.re_le_norm (spectrum T z)).trans (norm_spectrum_le T z)
      have := mul_le_mul_of_nonneg_left u (diff_nonneg f z)
      linarith [mul_nonneg (diff_nonneg f z) (mul_nonneg dp.le bp.le)]
    · rw [ite_eq_right hz,add_zero]
      have u : (spectrum T z).re ≤ δ*b := le_of_lt (by simpa [S] using hz)
      exact mul_le_mul_of_nonneg_left u (diff_nonneg f z)
  have bound := (bias_diff f T ε he.le hb).trans (sum_le_sum fun z _ => upper z)
  rw [sum_add_distrib,← sum_mul,sum_diff,one_mul] at bound
  have filterSum : (∑ z, if z ∈ S then diff f z*b else 0) = m*b := by simp [m,sum_mul]
  rw [filterSum] at bound
  have mass : δ ≤ m := by
    apply le_of_mul_le_mul_right (a := b) _ bp
    change ε^2*b ≤ δ*b + m*b at bound
    dsimp [δ] at bound ⊢
    linarith
  have mp : 0 < m := dp.trans_le mass
  refine ⟨conditioned (diff f) (diff_nonneg f) S mp,?_,?_⟩
  · intro z
    change δ * (if z ∈ S then diff f z/m else 0) ≤ diff f z
    by_cases hz : z ∈ S
    · rw [ite_eq_left hz,mul_div_assoc',div_le_iff₀ mp,mul_comm δ]
      exact mul_le_mul_of_nonneg_left mass (diff_nonneg f z)
    · simpa [hz] using diff_nonneg f z
  · intro z hz
    have mem : z ∈ S := by
      by_contra hn
      simp [conditioned,hn] at hz
    exact (mem_filter.mp mem).2

omit [Nonempty Y] in
/-- Pointwise support in the large spectrum implies a large average, so the
conditioning step can be iterated. -/
theorem bias_of_support (f : Law G) (T : Y → G →+ ZMod q) (δ : ℝ)
    (hs : ∀ z, 0 < f z → δ * Fintype.card Y ≤ (spectrum T z).re) :
    δ * Fintype.card Y ≤ ‖average f (spectrum T)‖ := by
  apply le_trans _ (Complex.re_le_norm _)
  rw [average,Complex.re_sum]
  calc
    _ = ∑ z, f z * (δ*Fintype.card Y) := by rw [← sum_mul,f.total,one_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro z _
      by_cases hz : 0 < f z
      · simpa using mul_le_mul_of_nonneg_left (hs z hz) (f.nonneg z)
      · have h := le_antisymm (le_of_not_gt hz) (f.nonneg z)
        simp [h]

end InducedDegreeRepetition.Duality
