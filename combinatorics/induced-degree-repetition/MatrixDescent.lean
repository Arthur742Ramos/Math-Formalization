module

public import ApproximateRectangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset Filter
open scoped Classical Topology
variable {q : ℕ} [NeZero q]

/-- At each depth, maximizing the excess of an allowed error budget over the actual
error ensures that either strip furnished by the image bound has acceptable error.
The depth is fixed in advance as a function of the requested cut scale. -/
theorem matrix_descent (hq : 3 ≤ q) (D ell e d : ℝ) (hD : 0 < D) (hell : 0 < ell)
    (he : 0 < e) (hd : 0 ≤ d) (k : ℕ) (cap : d+k*e ≤ 1/8) :
    ∀ᶠ r : ℕ in atTop, ∀ (X Y : Type) (A B : X → Y → ZMod q) (S : Finset X) (U : Finset Y),
      S.Nonempty → U.Nonempty → (∀ x ∈ S, ∀ y ∈ U, B x y = 0 ∨ B x y = 1) →
      errors (fun x y => A x y ≠ B x y) S U ≤ d*S.card*U.card → complexity A S U ≤ D*r →
      ∃ R ⊆ S, ∃ V ⊆ U, (e*Real.exp (-ell*r))^k*S.card ≤ R.card ∧
        (e*Real.exp (-ell*r))^k*U.card ≤ V.card ∧
        errors (fun x y => A x y ≠ B x y) R V ≤ (d+k*e)*R.card*V.card ∧
        complexity A R V ≤ complexity A S U/2^k + Real.log q := by
  induction k with
  | zero =>
    filter_upwards with r X Y A B S U hs hu bin low size
    refine ⟨S,Subset.rfl,U,Subset.rfl,by simp,by simp,by simpa using low,?_⟩
    simp only [pow_zero,div_one,le_add_iff_nonneg_right]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  | succ k ih =>
    have cap' : d+k*e ≤ 1/8 := by push_cast at cap; nlinarith
    filter_upwards [ih cap',approximation_rectangle hq D ell hD hell] with r prev rect
    intro X Y A B S U hs hu bin low size
    obtain ⟨R,rs,V,vu,hR,hV,low',size'⟩ := prev X Y A B S U hs hu bin low size
    let bad := fun x y => A x y ≠ B x y
    let δ := d+(k:ℝ)*e
    let m := Real.exp (-ell*r)
    have mp : 0 < m := Real.exp_pos _
    have m1 : m ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hell.le (Nat.cast_nonneg r : 0 ≤ (r:ℝ))])
    have rp : 0 < (R.card:ℝ) := lt_of_lt_of_le (mul_pos (pow_pos (mul_pos he mp) k)
      (by exact_mod_cast card_pos.mpr hs)) hR
    have vp : 0 < (V.card:ℝ) := lt_of_lt_of_le (mul_pos (pow_pos (mul_pos he mp) k)
      (by exact_mod_cast card_pos.mpr hu)) hV
    have dp : 0 ≤ δ := by dsimp [δ]; positivity
    have maxerr : δ+e ≤ 1/8 := by dsimp [δ]; push_cast at cap; nlinarith
    obtain ⟨R₀,rr,V₀,vv,hr,hv,rows,cols⟩ :=
      refine_errors bad R V (by exact_mod_cast rp) (by exact_mod_cast vp) δ e dp he low'
    have s : e ≤ e/(δ+e) := (le_div_iff₀ (by linarith)).mpr
      (mul_le_of_le_one_right he.le (by linarith))
    have lr := (mul_le_mul_of_nonneg_right s rp.le).trans hr
    have lv := (mul_le_mul_of_nonneg_right s vp.le).trans hv
    have rhs : R₀.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos he rp).trans_le lr)
    have vhs : V₀.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos he vp).trans_le lv)
    have rS := rr.trans rs
    have vU := vv.trans vu
    have mid := complexity_mono A rr vv
    obtain ⟨R₁,hr1,V₁,hv1,lr1,lv1,branch⟩ := rect X Y A B R₀ V₀ rhs vhs
      (fun x hx y hy => bin x (rS hx) y (vU hy)) ((rows _ Subset.rfl).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right maxerr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)))
      ((complexity_mono A rS vU).trans size)
    have sizes {a b c : ℝ} (h₁ : (e*m)^k*a ≤ b) (h₂ : e*b ≤ c) :
        (e*m)^(k+1)*a ≤ m*c := by
      calc
        _ = m*(e*((e*m)^k*a)) := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left h₁ he.le).trans h₂) mp.le
    have sr := sizes hR lr
    have sv := sizes hV lv
    have ra := sr.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) m1)
    have va := sv.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) m1)
    have step : (complexity A R₀ V₀+Real.log q)/2 ≤ complexity A S U/2^(k+1)+Real.log q := by
      have h := mid.trans size'
      rw [pow_succ,div_mul_eq_div_div]
      linarith
    have shift : d+((k+1:ℕ):ℝ)*e = δ+e := by dsimp [δ]; push_cast; ring
    rw [shift]
    rcases branch with h | h
    · exact ⟨R₁,hr1.trans rS,V₀,vU,sr.trans lr1,va,rows _ hr1,h.trans step⟩
    · exact ⟨R₀,rS,V₁,hv1.trans vU,ra,sv.trans lv1,cols _ hv1,h.trans step⟩

end InducedDegreeRepetition.Approximation
