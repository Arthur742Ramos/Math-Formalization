module

public import DualityEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical ComplexConjugate
variable {G Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] {q : ℕ} [NeZero q]

@[expose] noncomputable def phase (T : Y → G →+ ZMod q) (y : Y) (x : G) : ℂ := ZMod.stdAddChar (T y x)
@[expose] noncomputable def spectrum (T : Y → G →+ ZMod q) (x : G) : ℂ := ∑ y, phase T y x
@[expose] noncomputable def average (f : G → ℝ) (h : G → ℂ) : ℂ := ∑ x, (f x : ℂ) * h x

omit [Fintype Y] [Fintype G] in
theorem phase_sub (T : Y → G →+ ZMod q) (y : Y) (x z : G) :
    phase T y (x-z) = phase T y x * conj (phase T y z) := by
  simp only [phase,sub_eq_add_neg,map_add,map_neg,ZMod.stdAddChar_apply,AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv]
  congr 1
  exact Circle.coe_inv_eq_conj _

omit [Fintype G] in
theorem norm_spectrum_le (T : Y → G →+ ZMod q) (x : G) : ‖spectrum T x‖ ≤ Fintype.card Y := by
  calc
    _ ≤ ∑ y, ‖phase T y x‖ := norm_sum_le _ _
    _ = _ := by simp [phase,ZMod.stdAddChar_apply]

theorem average_spectrum (f : G → ℝ) (T : Y → G →+ ZMod q) :
    average f (spectrum T) = ∑ y, average f (phase T y) := by
  simp only [average,spectrum,mul_sum]
  exact sum_comm

omit [Fintype Y] in
/-- Reflection turns each Fourier coefficient of the difference law into the squared
absolute value of the corresponding coefficient of the original law. -/
theorem diff_phase (f : G → ℝ) (T : Y → G →+ ZMod q) (y : Y) :
    (∑ z, diff f z * (phase T y z).re) = ‖average f (phase T y)‖^2 := by
  rw [diff_test,← Complex.normSq_eq_norm_sq]
  have h : (∑ x, (f x : ℂ) * ∑ z, (f z : ℂ) * phase T y (x-z)) =
      average f (phase T y) * conj (average f (phase T y)) := by
    simp only [average,map_sum,map_mul,Complex.conj_ofReal,sum_mul,mul_sum,phase_sub]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro z _
    ring
  simpa [Complex.re_sum,Complex.mul_conj] using congrArg Complex.re h

theorem diff_spectrum (f : G → ℝ) (T : Y → G →+ ZMod q) :
    (∑ z, diff f z * (spectrum T z).re) = ∑ y, ‖average f (phase T y)‖^2 := by
  simp only [spectrum,Complex.re_sum,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => diff_phase f T y

/-- Bias survives differencing, in the real part and with a squared loss. -/
theorem bias_diff [Nonempty Y] (f : G → ℝ) (T : Y → G →+ ZMod q) (ε : ℝ) (he : 0 ≤ ε)
    (hb : ε * Fintype.card Y ≤ ‖average f (spectrum T)‖) :
    ε^2 * Fintype.card Y ≤ ∑ z, diff f z * (spectrum T z).re := by
  rw [diff_spectrum]
  rw [average_spectrum] at hb
  have h := hb.trans (norm_sum_le _ _)
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset Y) (fun _ => (1:ℝ))
    (fun y => ‖average f (phase T y)‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at hc
  have hp : 0 < (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs := (sq_le_sq₀ (mul_nonneg he hp.le) (sum_nonneg fun _ _ => norm_nonneg _)).mpr h
  apply le_of_mul_le_mul_left (a := (Fintype.card Y : ℝ)) _ hp
  nlinarith

end InducedDegreeRepetition.Duality
