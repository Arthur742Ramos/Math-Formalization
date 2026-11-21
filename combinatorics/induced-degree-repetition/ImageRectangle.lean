module

public import DualityRows
public import DualityBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset Filter Duality
open scoped Classical Topology

/-- On groups of size at most exp(Dr), the loss in the weighted rectangle theorem
is smaller than exp(ηr) for any fixed η>0 and all sufficiently large r. -/
theorem rectangle_of_image_size (q : ℕ) (hq : 3 ≤ q) [NeZero q] (D η : ℝ) (_hD : 0 < D)
    (he : 0 < η) : ∀ᶠ r : ℕ in atTop,
    ∀ (G X Y : Type) [AddCommGroup G] [Fintype G] [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y],
      (∀ z : G, q • z = 0) → Real.log (Fintype.card G) ≤ D*r →
      ∀ (v : X → G) (T : Y → G →+ ZMod q),
      (Fintype.card X : ℝ)*Fintype.card Y/4 ≤ ‖∑ x, ∑ y, ZMod.stdAddChar (T y (v x))‖ →
      ∃ (S : Finset X) (U : Finset Y) (t : ZMod q),
        Real.exp (-η*r)*Fintype.card X ≤ S.card ∧ Real.exp (-η*r)*Fintype.card Y ≤ U.card ∧
          ∀ x ∈ S, ∀ y ∈ U, T y (v x) = t := by
  classical
  obtain ⟨C,hC⟩ := coset_concentration q (by omega)
  let δ : ℝ := η/(6*(C+1))
  have dp : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L,hL⟩ := exists_nat_gt (D/δ)
  have dL : D < δ*L := by simpa [mul_comm] using (div_lt_iff₀ dp).mp hL
  let ρ := (1/8 : ℝ)^(2^(L+1))
  have rp : 0 < ρ := by dsimp [ρ]; positivity
  have r1 : ρ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have rc : ρ ≤ cutoff (L+1) := by change ρ ≤ 2*ρ; linarith
  have qpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0<q)
  let B := (ρ/(q:ℝ))^(L+1)*(ρ^2*ρ^(C*3)/q)
  have bp : 0 < B := by dsimp [B]; positivity
  have decay : 3*(C:ℝ)*δ ≤ η/2 := by
    dsimp [δ]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r₀,hr⟩ := exists_nat_gt (max (max (Real.log 2/δ) (-Real.log B/(η/2))) 0)
  filter_upwards [eventually_ge_atTop r₀] with r rr
  have rt : max (max (Real.log 2/δ) (-Real.log B/(η/2))) 0 < (r:ℝ) := hr.trans_le (by exact_mod_cast rr)
  have rp' : 0 < (r:ℝ) := (le_max_right _ _).trans_lt rt
  have k2 := (div_lt_iff₀ dp).mp ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt rt))
  have rB := (div_lt_iff₀ (by positivity : 0 < η/2)).mp
    ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt rt))
  let K := Real.exp (δ*r)
  have kp : 0 < K := Real.exp_pos _
  have hk : 2 ≤ K := (Real.log_le_iff_le_exp (by norm_num)).mp (by linarith)
  have loss : Real.exp (-η*r) ≤ fraction q C L ρ K := by
    have e : fraction q C L ρ K = B/K^(C*3) := by
      dsimp [fraction,B]
      rw [div_pow,← pow_mul,← pow_mul]
      field_simp
      rw [← pow_mul,div_pow,div_mul_cancel₀ _ (pow_ne_zero _ rp.ne')]
    rw [e,div_eq_mul_inv,← Real.exp_log bp]
    change _ ≤ Real.exp _ * ((Real.exp (δ*r))^(C*3))⁻¹
    rw [← Real.exp_nat_mul,← Real.exp_neg,← Real.exp_add,Real.exp_le_exp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right decay rp'.le]
  intro G X Y groupG finiteG finiteX nonemptyX finiteY nonemptyY tor size v T hb
  let f := empirical v
  have budget : (Fintype.card G : ℝ) < K^L := by
    change _ < (Real.exp (δ*r))^L
    rw [← Real.exp_nat_mul,← Real.log_lt_iff_lt_exp (by exact_mod_cast Fintype.card_pos)]
    exact size.trans_lt (by nlinarith [mul_lt_mul_of_pos_right dL rp'])
  have bias : (1/4:ℝ)*Fintype.card Y ≤ ‖average f (spectrum T)‖ := by
    have e := congrArg norm (empirical_average v (spectrum T))
    simp only [norm_mul,Complex.norm_natCast] at e
    change (Fintype.card X:ℝ)*‖average f (spectrum T)‖ = _ at e
    change _ ≤ ‖∑ x, spectrum T (v x)‖ at hb
    rw [← e] at hb
    apply le_of_mul_le_mul_left (a := (Fintype.card X:ℝ)) _ (by exact_mod_cast Fintype.card_pos)
    linarith
  obtain ⟨S,U,t,hs,hu,hm⟩ := rectangle_bound f T C L ρ K rp r1 hk rc budget bias fun g hg =>
    hC tor g.val g.nonneg g.total (K/ρ) ((le_div_iff₀ rp).mpr (by linarith)) hg
  refine ⟨univ.filter (fun x => v x ∈ S),U,t,?_,
    (mul_le_mul_of_nonneg_right loss (Nat.cast_nonneg _)).trans hu,fun x hx y hy => hm _ (mem_filter.mp hx).2 y hy⟩
  exact (mul_le_mul_of_nonneg_right (loss.trans hs) (Nat.cast_nonneg _)).trans_eq (empirical_mass v S)

end InducedDegreeRepetition.Approximation
