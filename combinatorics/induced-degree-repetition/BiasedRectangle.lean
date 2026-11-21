module

public import RemainingStatements
public import DualityLoss
public import DualityRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Finset Duality
open scoped Classical

/-- Lemma 4. Empirical row probabilities retain repeated input labels. Difference
conditioning forces a stable energy scale, where Lemma 6 and character
orthogonality give the rectangle. -/
theorem biased_rectangle : BiasedRectangle := by
  classical
  intro q hq inst
  obtain ⟨C,hC⟩ := coset_concentration q (by omega)
  refine ⟨lossConstant q C,?_,?_⟩
  · have lq := Real.log_pos (show 1 < (q:ℝ) by exact_mod_cast (by omega : 1 < q))
    have l8 := Real.log_pos (show (1:ℝ) < 8 by norm_num)
    unfold lossConstant
    positivity
  intro n a b ha hb v w hBias
  let : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0,hb⟩⟩
  let G := Fin n → ZMod q
  let T (y : Fin b) : G →+ ZMod q :=
    { toFun := fun x => x ⬝ᵥ w y
      map_zero' := zero_dotProduct _
      map_add' := fun _ _ => add_dotProduct _ _ _ }
  let f := empirical v
  let L := rounds n
  let K := growth q n
  let ρ := floorBias n
  have hp : 0 < ρ := by dsimp [ρ,floorBias]; positivity
  have hr1 : ρ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have bound : ρ ≤ cutoff (L+1) := by change ρ ≤ 2*ρ; linarith
  have lp := rounds_pos n
  have q2 : 2 ≤ (q:ℝ) := by exact_mod_cast (by omega : 2 ≤ q)
  have kk : 2 ≤ K := by
    change 2 ≤ (q:ℝ)^(n/rounds n+1)
    exact q2.trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero _))
  have budget : (Fintype.card G : ℝ) < K^L := by
    dsimp [G,K,growth,L]
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,← pow_mul]
    apply pow_lt_pow_right₀ (by linarith)
    have rem := Nat.mod_lt n lp
    have eq := Nat.div_add_mod n (rounds n)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (n/rounds n)]
    omega
  have bias : (1/4:ℝ)*Fintype.card (Fin b) ≤ ‖average f (spectrum T)‖ := by
    have e := congrArg norm (empirical_average v (spectrum T))
    simp only [norm_mul,Complex.norm_natCast,Fintype.card_fin] at e
    change (a:ℝ)*‖average f (spectrum T)‖ = ‖∑ x, ∑ y, ZMod.stdAddChar (v x ⬝ᵥ w y)‖ at e
    rw [← e] at hBias
    rw [Fintype.card_fin]
    apply le_of_mul_le_mul_left (a := (a:ℝ)) _ (by exact_mod_cast ha)
    linarith
  obtain ⟨S,U,t,hs,hu,hm⟩ := rectangle_bound f T C L ρ K hp hr1 kk bound budget bias
    (fun g hg => hC (ZModModule.char_nsmul_eq_zero q) g.val g.nonneg g.total (K/ρ)
      ((le_div_iff₀ hp).mpr (by linarith)) hg)
  have cost := loss_le_fraction q C n (by omega)
  refine ⟨univ.filter (fun i => v i ∈ S),U,t,?_,?_,?_⟩
  · have m := empirical_mass v S
    rw [Fintype.card_fin] at m
    have hs' : _ ≤ ∑ x ∈ S, empirical v x := cost.trans hs
    have upper := mul_le_mul_of_nonneg_right hs' (Nat.cast_nonneg a : (0:ℝ) ≤ a)
    rw [m] at upper
    convert upper using 1
    · simp [scale]
    · apply congrArg Nat.cast
      apply congrArg Finset.card
      ext i
      simp
  · rw [Fintype.card_fin] at hu
    simpa [scale] using (mul_le_mul_of_nonneg_right cost (Nat.cast_nonneg b)).trans hu
  · intro x hx y hy
    exact hm _ (mem_filter.mp hx).2 y hy

end InducedDegreeRepetition.OpenProblems
