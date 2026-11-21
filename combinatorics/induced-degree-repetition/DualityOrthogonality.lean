module

public import DualitySpectrum
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical ComplexConjugate
variable {G Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] {q : ℕ} [NeZero q]

@[expose] def trace (T : Y → G →+ ZMod q) (H : AddSubgroup G) (y : Y) : H →+ ZMod q :=
  (T y).comp H.subtype

omit [Fintype G] [Fintype Y] in
theorem std_sub (a b : ZMod q) :
    ZMod.stdAddChar (a-b) = ZMod.stdAddChar a * conj (ZMod.stdAddChar b) := by
  simpa [phase] using phase_sub (fun _ : Unit => AddMonoidHom.id (ZMod q)) () a b

omit [Fintype Y] in
theorem trace_orthogonality (T : Y → G →+ ZMod q) (H : AddSubgroup G) (z : G) (i j : Y) :
    (∑ h : H, (phase T i (z+h) * conj (phase T j (z+h))).re) ≤
      if trace T H i = trace T H j then (Fintype.card H : ℝ) else 0 := by
  classical
  by_cases agree : trace T H i = trace T H j
  · rw [ite_eq_left agree]
    calc
      _ ≤ ∑ _h : H, (1 : ℝ) := by
        apply sum_le_sum
        intro h _
        apply (Complex.re_le_norm _).trans
        simp [phase,ZMod.stdAddChar_apply]
      _ = _ := by simp
  · rw [ite_eq_right agree]
    let D := trace T H i - trace T H j
    let χ := ZMod.stdAddChar.compAddMonoidHom D
    have hn : χ ≠ 1 := by
      intro hc
      apply agree
      ext h
      have eq : ZMod.stdAddChar (D h) = ZMod.stdAddChar (0 : ZMod q) := by
        change χ h = _
        rw [hc]
        simp
      exact sub_eq_zero.mp (ZMod.injective_stdAddChar eq)
    have hs : ∑ h : H, χ h = 0 := AddChar.sum_eq_zero_of_ne_one hn
    have factor (h : H) : phase T i (z+h) * conj (phase T j (z+h)) =
        (phase T i z * conj (phase T j z)) * χ h := by
      simp only [phase,map_add,AddChar.map_add_eq_mul,map_mul,χ,D,AddChar.compAddMonoidHom_apply,
        AddMonoidHom.sub_apply,std_sub,trace,AddMonoidHom.comp_apply,AddSubgroup.subtype_apply]
      ring
    simp_rw [factor]
    rw [← Complex.re_sum,← mul_sum,hs,mul_zero,Complex.zero_re]

/-- The squared character sum over a coset is bounded by its size times the number
of ordered column pairs with the same restriction to the subgroup. -/
theorem coset_spectrum_bound (T : Y → G →+ ZMod q) (H : AddSubgroup G) (z : G) :
    (∑ h : H, ‖spectrum T (z+h)‖^2) ≤
      (Fintype.card H : ℝ) * ∑ i : Y, ((univ.filter fun j => trace T H i = trace T H j).card : ℝ) := by
  classical
  have expand (x : G) : ‖spectrum T x‖^2 =
      ∑ i, ∑ j, (phase T i x * conj (phase T j x)).re := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.ofReal_re (Complex.normSq _),← Complex.mul_conj]
    simp only [spectrum,map_sum,sum_mul,mul_sum,Complex.re_sum]
    rw [sum_comm]
  simp_rw [expand]
  rw [sum_comm]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [sum_comm]
  calc
    _ ≤ ∑ j : Y, if trace T H i = trace T H j then (Fintype.card H : ℝ) else 0 :=
      sum_le_sum fun j _ => trace_orthogonality T H z i j
    _ = _ := by simp [← sum_filter,mul_comm]

end InducedDegreeRepetition.Duality
