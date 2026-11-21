module

public import MatrixDescent
public import TerminalRectangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset Filter
open scoped Classical Topology
variable {q : ℕ} [NeZero q]

/-- Low disagreement on a matrix of image complexity at most Dr implies a
constant rectangle with both relative sides above exp(-v r), on which the error
density remains bounded by 4qd. The initial tolerance d is independent of D,v. -/
theorem rigidity_estimate (hq : 3 ≤ q) (d v D : ℝ) (hd : 0 < d) (hs : d ≤ 1/16)
    (hv : 0 < v) (hD : 0 < D) :
    ∀ᶠ r : ℕ in atTop, ∀ (X Y : Type) (A B : X → Y → ZMod q) (S : Finset X) (U : Finset Y),
      S.Nonempty → U.Nonempty → (∀ x ∈ S, ∀ y ∈ U, B x y = 0 ∨ B x y = 1) →
      errors (fun x y => A x y ≠ B x y) S U ≤ d*S.card*U.card → complexity A S U ≤ D*r →
      ∃ R ⊆ S, ∃ V ⊆ U, ∃ t : ZMod q, Real.exp (-v*r)*S.card ≤ R.card ∧
        Real.exp (-v*r)*U.card ≤ V.card ∧ (∀ x ∈ R, ∀ y ∈ V, A x y = t) ∧
        errors (fun x y => A x y ≠ B x y) R V ≤ 4*d*q*R.card*V.card := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (show 0 < v/(4*D) by positivity) (by norm_num : (1/2:ℝ)<1)
  have reduce : D/2^k ≤ v/4 := by
    rw [one_div,inv_pow,inv_eq_one_div,div_lt_div_iff₀ (by positivity) (by positivity)] at hk
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let e := d/(k+1)
  let ell := v/(4*(k+1))
  have ep : 0 < e := by dsimp [e]; positivity
  have lp : 0 < ell := by dsimp [ell]; positivity
  have ee : (k:ℝ)*e ≤ d := by
    dsimp [e]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith
  have ll : (k:ℝ)*ell ≤ v/4 := by
    dsimp [ell]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith
  have qp : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0<q)
  obtain ⟨r₀,hr⟩ := exists_nat_gt (Real.log (2*q/e^k)/(v/2))
  filter_upwards [eventually_ge_atTop r₀, matrix_descent hq D ell e d hD lp ep hd.le k (by linarith)] with r rr descent
  intro X Y A B S U s u bin low comp
  let t := Real.exp (-v*r)
  let F := 2*(q:ℝ)*Real.exp (v*r/4)
  let f := (e*Real.exp (-ell*r))^k
  have r0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hp : 0 < F := by dsimp [F]; positivity
  have bound : t*F ≤ f := by
    have threshold := (div_lt_iff₀ (by positivity : 0 < v/2)).mp (hr.trans_le (show (r₀:ℝ) ≤ r by exact_mod_cast rr))
    have h := (Real.log_le_iff_le_exp (by positivity : 0 < 2*(q:ℝ)/e^k)).mp threshold.le
    have h' := (div_le_iff₀ (pow_pos ep k)).mp h
    have hl := mul_le_mul_of_nonneg_right ll r0
    calc
      _ = 2*q*Real.exp (-v*r + v*r/4) := by dsimp [t,F]; rw [Real.exp_add]; ring
      _ ≤ (Real.exp ((r:ℝ)*(v/2))*e^k)*Real.exp (-v*r+v*r/4) :=
        mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
      _ = e^k*Real.exp ((r:ℝ)*(v/2)+(-v*r+v*r/4)) := by
        conv_rhs => rw [Real.exp_add]
        ring
      _ ≤ e^k*Real.exp ((k:ℝ)*(-ell*r)) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hl])) (pow_nonneg ep.le k)
      _ = _ := by dsimp [f]; rw [Real.exp_nat_mul,mul_pow]
  obtain ⟨R,rs,V,vu,hR,hV,lo,co⟩ := descent X Y A B S U s u bin low comp
  have fp : 0 < f := by dsimp [f]; positivity
  have rp : R.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos fp (show (0:ℝ)<S.card by exact_mod_cast card_pos.mpr s)).trans_le hR)
  have vp : V.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos fp (show (0:ℝ)<U.card by exact_mod_cast card_pos.mpr u)).trans_le hV)
  have lo' := lo.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (show d+k*e ≤ 2*d by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  obtain ⟨R',rr',V',vv',z,lr,lv,con,err⟩ :=
    terminal_rectangle A _ R V rp vp (2*d) (by linarith) lo'
  have cc : complexity A R V ≤ Real.log q + v*r/4 := by
    apply co.trans
    have a := div_le_div_of_nonneg_right comp (show (0:ℝ) ≤ 2^k by positivity)
    have b := mul_le_mul_of_nonneg_right reduce r0
    rw [mul_div_right_comm] at a
    linarith
  have cu : 2*Real.exp (complexity A R V) ≤ F := by
    have h := Real.exp_le_exp.mpr cc
    rw [Real.exp_add,Real.exp_log qp] at h
    dsimp [F]
    linarith
  have cr : 2*(q:ℝ) ≤ F := le_mul_of_one_le_right (by positivity)
    (Real.one_le_exp_iff.mpr (by positivity))
  have est {a b c : ℝ} (ha : 0 ≤ a) (hb : f*a ≤ b) (hc : b ≤ F*c) : t*a ≤ c := by
    apply le_of_mul_le_mul_left (a := F) _ hp
    linarith only [(mul_le_mul_of_nonneg_right bound ha).trans (hb.trans hc)]
  exact ⟨R',rr'.trans rs,V',vv'.trans vu,z,
    est (Nat.cast_nonneg _) hR (lr.trans (mul_le_mul_of_nonneg_right cr (Nat.cast_nonneg _))),
    est (Nat.cast_nonneg _) hV (lv.trans (mul_le_mul_of_nonneg_right cu (Nat.cast_nonneg _))),con,by linarith⟩

end InducedDegreeRepetition.Approximation
