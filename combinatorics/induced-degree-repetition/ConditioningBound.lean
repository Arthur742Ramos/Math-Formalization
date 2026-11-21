module

public import PrescriptionCount
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Residues

open Finset Filter
open scoped Classical Topology
variable {P Y : Type*}

/-- Average the atom estimate over testers, bounding exceptional lists by the total
number of tuples. Compare with the double count from the conditional family. -/
theorem conditioning_impossible (Q F : Finset P) (E : Finset Y) (n : ℕ) (ok : P → Y → Prop)
    (bad : (Fin n → Y) → Prop) (α δ γ ξ : ℝ) (hp : 0<ξ) (hhalf : ξ ≤ 1/2)
    (dn : 0 ≤ δ) (fn : F.Nonempty) (en : E.Nonempty) (sub : Q ⊆ F)
    (mass : α*F.card ≤ Q.card)
    (rate : δ+γ < α/2*(1-2*ξ)^n)
    (high : ∀ y ∈ E, (1-ξ)*Q.card ≤ ((Q.filter fun p => ok p y).card:ℝ))
    (per : ∀ ys ∈ Fintype.piFinset (fun _ : Fin n => E), ¬bad ys →
      ((F.filter fun p => ∀ i, ok p (ys i)).card:ℝ) ≤ δ*F.card)
    (rare : (((Fintype.piFinset (fun _ : Fin n => E)).filter bad).card:ℝ) ≤
      γ*(Fintype.piFinset (fun _ : Fin n => E)).card) : False := by
  classical
  let T := Fintype.piFinset (fun _ : Fin n => E)
  have lower := agreement_lower Q E en ok ξ hp hhalf n high
  rw [← double_count] at lower
  have upper (ys : Fin n → Y) (hy : ys ∈ T) :
      ((Q.filter (fun p => ∀ i, ok p (ys i))).card:ℝ) ≤ δ*F.card + (if bad ys then (1:ℝ) else 0)*F.card := by
    have le : (Q.filter (fun p => ∀ i, ok p (ys i))).card ≤ (F.filter (fun p => ∀ i, ok p (ys i))).card :=
      card_le_card (filter_subset_filter _ sub)
    by_cases h : bad ys
    · rw [ite_eq_left h,one_mul]
      exact (Nat.cast_le.mpr (le.trans (card_filter_le ..))).trans (le_add_of_nonneg_left (mul_nonneg dn (Nat.cast_nonneg _)))
    · simpa only [ite_eq_right h,zero_mul,add_zero] using (Nat.cast_le.mpr le).trans (per ys hy h)
  have bound := lower.trans (sum_le_sum (s := T) upper)
  simp only [sum_add_distrib,← sum_mul,sum_boole,sum_const,nsmul_eq_mul] at bound
  have ub : Q.card/2*((1-2*ξ)*E.card)^n ≤ (δ+γ)*F.card*T.card := by
    apply bound.trans
    have be : ((T.filter bad).card:ℝ)*F.card ≤ γ*T.card*F.card := mul_le_mul_of_nonneg_right rare (Nat.cast_nonneg _)
    linarith only [be]
  have te : (T.card:ℝ) = (E.card:ℝ)^n := by simp [T]
  rw [mul_pow,← te] at ub
  have tp : 0 < (T.card:ℝ) := by rw [te]; exact pow_pos (by exact_mod_cast card_pos.mpr en) _
  have fp : 0 < (F.card:ℝ) := by exact_mod_cast card_pos.mpr fn
  have b := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right rate fp) tp
  have m := mul_le_mul_of_nonneg_right mass (mul_nonneg (pow_nonneg (by linarith : 0 ≤ 1-2*ξ) n) tp.le)
  linarith only [m,b,ub]

theorem conditioning_rates (D A C β : ℝ) (L : ℕ) (gap : D < A)
    (hC : 0 < C) (hb : 0 < β) (hL : 0 < L) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/2 ∧ ∀ᶠ r : ℕ in atTop,
      Real.exp (-A*r)+L*Real.exp (-β*(r:ℝ)^2) <
        Real.exp (-D*r)/2*(1-2*ξ)^⌈C*r⌉₊ := by
  let v := (A-D)/(2*(C+1))
  have vp : 0 < v := by dsimp [v]; positivity [sub_pos.mpr gap]
  let ξ := (1-Real.exp (-v))/2
  have rp := Real.exp_pos (-v)
  have less := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr vp)
  refine ⟨ξ,by dsimp [ξ]; linarith,by dsimp [ξ]; linarith,?_⟩
  have eq : 1-2*ξ = Real.exp (-v) := by dsimp [ξ]; ring
  have lg : 0 ≤ Real.log (L:ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have vC : v*(C+1) = (A-D)/2 := by dsimp [v]; field_simp
  obtain ⟨r₀,h₀⟩ := exists_nat_gt (max ((A+Real.log L)/β) (2*Real.log 4/(A-D)))
  filter_upwards [eventually_ge_atTop r₀,eventually_ge_atTop 1] with r rr r1
  have rpos : 0 < (r:ℝ) := by exact_mod_cast r1
  have one : 1 ≤ (r:ℝ) := by exact_mod_cast r1
  have large := h₀.trans_le (by exact_mod_cast rr : (r₀:ℝ) ≤ r)
  have quad := (div_lt_iff₀ hb).mp ((le_max_left ..).trans_lt large)
  have lin := (div_lt_iff₀ (sub_pos.mpr gap)).mp ((le_max_right ..).trans_lt large)
  have small : (L:ℝ)*Real.exp (-β*(r:ℝ)^2) ≤ Real.exp (-A*r) := by
    rw [← Real.exp_log (show (0:ℝ)<L by exact_mod_cast hL),← Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right quad.le rpos.le,le_mul_of_one_le_right lg one]
  apply (add_le_add_right small _).trans_lt
  rw [← two_mul,eq,← Real.exp_nat_mul]
  have ceil : (⌈C*r⌉₊:ℝ) ≤ (C+1)*r := by
    have e := Nat.ceil_lt_add_one (show 0 ≤ C*(r:ℝ) by positivity)
    linarith
  rw [div_mul_eq_mul_div,lt_div_iff₀ (by norm_num : (0:ℝ)<2)]
  have factor : 2*Real.exp (-A*r)*2 = Real.exp (Real.log 4 - A*r) := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num)]; ring_nf
  rw [factor,← Real.exp_add,Real.exp_lt_exp]
  nlinarith [mul_le_mul_of_nonneg_left ceil vp.le,congrArg (·*(r:ℝ)) vC]

end InducedDegreeRepetition.Residues
