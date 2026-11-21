module

public import SmallSample
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Restriction Finset Filter
open scoped Classical Topology

set_option maxHeartbeats 400000 in
/-- Lemma 7. The exponent controlling the mass of a projected row is chosen
before the subgroup budget D. -/
theorem random_restrictions : RandomRestrictions := by
  classical
  intro q hq u τ c hu hτ hc
  let a := u/128
  have ap : 0 < a := by dsimp [a]; positivity
  refine ⟨a,ap,?_⟩
  intro D hd
  have inst : NeZero q := ⟨by omega⟩
  obtain ⟨C,hC,prob⟩ := small_sample_probability (q := q) hq u τ c D hu hτ hc hd
  refine ⟨C,a,by linarith,ap,?_⟩
  filter_upwards [prob] with r upper
  intro N G B X Y core dis lx ly
  let n := ⌈C*r⌉₊
  let A := fun (x:X) (y:Y) => adjMod q G x y
  let P := fun (ys : Fin n → Y) => HeavyRestriction q G X (forget ys) r D a
  let w := Real.exp (-a*r*n) * Fintype.card (Fin n → X)
  have bound (ys : Fin n → Y) : (if P ys then (1:ℝ) else 0)*w ≤ ∑ xs : Fin n → X,
      if smallSample A xs ys (q*Real.exp (D*r)) then (1:ℝ) else 0 := by
    by_cases h : P ys
    · simpa only [ite_eq_left h,one_mul] using heavy_chance G X Y D a ys h
    · simp only [ite_eq_right h,zero_mul]
      exact sum_nonneg fun _ _ => by split <;> norm_num
  have e := sum_le_sum (s := (univ : Finset (Fin n → Y))) fun ys _ => bound ys
  rw [← sum_mul,sum_comm] at e
  have h := e.trans (upper N G B X Y core dis lx ly)
  have cutp := (Real.exp_pos _).trans_le core.1
  have bp : 0 < (B.card:ℝ) := pos_of_mul_pos_left cutp (Real.exp_pos _).le
  have xp : 0 < (X.card:ℝ) := (mul_pos bp (Real.exp_pos _)).trans_le lx.2
  let : Nonempty X := (card_pos.mp (by exact_mod_cast xp)).to_subtype
  have wx : (0:ℝ) < Fintype.card (Fin n → X) := by exact_mod_cast Fintype.card_pos
  let T := Fintype.piFinset (fun _ : Fin n => Y)
  let E := T.filter fun ys => HeavyRestriction q G X ys r D a
  have event : (E.card:ℝ) = ∑ ys : Fin n → Y, if P ys then 1 else 0 := by
    convert count_label_event (I := Fin n) Y (fun ys => HeavyRestriction q G X ys r D a) using 1
    · apply congrArg Nat.cast
      apply congrArg Finset.card
      ext v
      simp [E,T,Fintype.mem_piFinset]
    · apply sum_congr (Finset.ext fun _ => by simp)
      intro v _
      rfl
  rw [← event] at h
  have ty : (Fintype.card (Fin n → Y):ℝ) = T.card := by
    simp [T,Fintype.card_piFinset]
  let den := Real.exp (-a*r*n)
  have hn : (r:ℝ) ≤ n := (le_mul_of_one_le_left (Nat.cast_nonneg _) hC).trans (Nat.le_ceil _)
  have rate : Real.exp (-u*r*n/64) ≤ Real.exp (-a*(r:ℝ)^2)*den := by
    dsimp [den,a]
    rw [← Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hn (mul_nonneg hu.le (Nat.cast_nonneg r : (0:ℝ)≤r))]
  change (E.card:ℝ) ≤ Real.exp (-a*(r:ℝ)^2)*T.card
  apply le_of_mul_le_mul_right (a := w) _ (mul_pos (Real.exp_pos _) wx)
  apply h.trans
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right rate wx.le) (Nat.cast_nonneg _))
  rw [ty]
  dsimp [w,den]
  apply le_of_eq
  ring

end InducedDegreeRepetition.OpenProblems
