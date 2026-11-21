module

public import DensityExtraction
public import DensityRefinement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.OpenProblems

open Finset Filter Real

/-- Lemma 3. Every sufficiently large host either has an exactly regular witness in
the requested size interval, or contains an exponentially large uniformly dense core
whose centered normalized adjacency operator has small Euclidean norm. -/
theorem density_reduction : DensityReduction := by
  intro K hK
  let c := 1/(2*K)
  have cp : 0 < c := by dsimp [c]; positivity
  have cK : c*(2*K) = 1 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨u,τ,r₀,up,tp,extract⟩ := regular_or_two_sided c cp
  refine ⟨u/2,τ/2,c/2,2*c,by positivity,by positivity,by positivity,by positivity,?_⟩
  intro ε hε
  obtain ⟨D,n,dpos,refineCore⟩ := refine_two_sided_cuts τ ε tp hε
  let scale := fun N : ℕ => K*log N
  let order := fun N => ⌈scale N⌉₊
  have large : Tendsto scale atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hK).mpr (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have orderLarge : Tendsto order atTop atTop := tendsto_nat_ceil_atTop.comp large
  have bound (b M : ℝ) (hb : 0 < b) : ∀ᶠ N : ℕ in atTop, M ≤ exp (b*order N) := by
    filter_upwards [orderLarge.eventually_ge_atTop ⌈M/b⌉₊] with N hN
    have hh := (div_le_iff₀ hb).mp ((Nat.le_ceil _).trans (Nat.cast_le.mpr hN))
    linarith [add_one_le_exp (b*order N)]
  filter_upwards [large.eventually_ge_atTop 1,orderLarge.eventually_ge_atTop r₀,
    bound (u/2) (4*D) (by positivity),bound (c/4) D (by positivity),
    bound (3*c/4) n (by positivity),eventually_ge_atTop (1:ℕ)] with N hsc hr hD hD' hn hN
  intro G
  let r := order N
  have npos : 0 < (N:ℝ) := by exact_mod_cast hN
  have ceil := Nat.ceil_lt_add_one (show 0 ≤ scale N by linarith)
  have lo : exp (c*r) ≤ N := (le_log_iff_exp_le npos).mp (by
    have h : (r:ℝ) ≤ 2*(K*log N) := by dsimp [r,order,scale] at *; linarith
    apply (le_of_mul_le_mul_right (a := 2*K) _ (by positivity))
    calc
      c*r*(2*K) = r := by rw [mul_right_comm, cK, one_mul]
      _ ≤ _ := by linarith)
  have hi : (N:ℝ) ≤ exp (2*c*r) := (log_le_iff_le_exp npos).mp (by
    have h := Nat.le_ceil (scale N)
    change K*log N ≤ (r:ℝ) at h
    apply le_of_mul_le_mul_right (a := K) _ hK
    calc
      log N*K ≤ r := by linarith
      _ = 2*c*r*K := by nlinarith [congrArg (fun z : ℝ => z*(r:ℝ)) cK])
  rcases extract r hr N G lo hi with reg | ⟨W,hW,cuts⟩
  · exact Or.inl reg
  right
  have dR : (0:ℝ) < D := Nat.cast_pos.mpr dpos
  have rate : 4*(D:ℝ) ≤ exp (u*r) := hD.trans (exp_le_exp.mpr (by
    nlinarith [mul_nonneg up.le (Nat.cast_nonneg r)]))
  have suff : 4*(D:ℝ) * (W.card*exp (-u*r)) ≤ W.card := by
    have h := mul_le_mul_of_nonneg_right rate (exp_pos (-u*r)).le
    rw [← exp_add,show u*r + -u*r = 0 by ring, exp_zero] at h
    nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg W.card)]
  have orderW : n ≤ W.card := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans hn
    simpa only [r,mul_div_right_comm] using hW
  obtain ⟨B,p,hBW,sz,hpl,hpu,cutB,deg,spec⟩ := refineCore G W _ orderW suff cuts
  have hsz : (W.card : ℝ) ≤ D*B.card := by exact_mod_cast sz
  refine ⟨B,p,?_,?_,hpl,hpu,?_,deg,spec⟩
  · apply le_of_mul_le_mul_right (a := (D:ℝ)) _ dR
    calc
      exp (c/2*r) * D ≤ exp (c/2*r) * exp (c/4*r) := mul_le_mul_of_nonneg_left hD' (exp_pos _).le
      _ = exp (3*c*r/4) := by rw [← exp_add]; congr 1; ring
      _ ≤ _ := hW.trans (hsz.trans_eq (mul_comm ..))
  · exact (Nat.cast_le.mpr (by simpa using card_le_univ B)).trans hi
  · have subcut : (W.card : ℝ)*exp (-u*r) ≤ B.card*exp (-(u/2)*r) := by
      have dsmall : (D:ℝ) ≤ exp (u/2*r) := (by linarith : (D:ℝ) ≤ 4*D).trans hD
      calc
        _ ≤ (D*B.card:ℝ)*exp (-u*r) := mul_le_mul_of_nonneg_right hsz (exp_pos _).le
        _ ≤ (B.card:ℝ) * (exp (u/2*r)*exp (-u*r)) := by
          nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left dsmall (Nat.cast_nonneg B.card))
            (exp_pos (-u*r)).le]
        _ = _ := by rw [← exp_add]; congr 2; ring
    intro X hX Y hY hd hx hy b
    have H := cutB X hX Y hY hd (subcut.trans hx) (subcut.trans hy) b
    exact le_trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right (show τ/2 ≤ τ by linarith) (Nat.cast_nonneg _)) H

end InducedDegreeRepetition.OpenProblems
