module

public import DualityIteration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {G : Type} {Y : Type*} [AddCommGroup G] [Fintype G] [Fintype Y] [Nonempty Y]
  {q : ℕ} [NeZero q]

/-- Explicit loss for L energy tests, including the initial conditioning step. -/
@[expose] noncomputable def fraction (q C L : ℕ) (ρ K : ℝ) : ℝ :=
  (ρ/q)^(L+1) * (ρ^2 / ((K/ρ)^C)^3 / q)

theorem rectangle_bound (f : Law G) (T : Y → G →+ ZMod q) (C L : ℕ) (ρ K : ℝ)
    (hr : 0 < ρ) (hr1 : ρ ≤ 1) (hK : 2 ≤ K) (hrL : ρ ≤ cutoff (L+1))
    (budget : (Fintype.card G : ℝ) < K^L)
    (bias : (1/4 : ℝ)*Fintype.card Y ≤ ‖average f (spectrum T)‖)
    (conc : ∀ g : Law G, normSq g / (K/ρ)^2 ≤ normSq (convolution g g) →
      ∃ (H : AddSubgroup G) (z : G), (Nat.card H : ℝ) ≤ (K/ρ)^C / normSq g ∧
        1/(K/ρ)^C ≤ massOn g {x | x-z ∈ H}) :
    Rectangle f T (fraction q C L ρ K) (fraction q C L ρ K * Fintype.card Y) := by
  classical
  let P := (K/ρ)^C
  let α := ρ^2/P^3/q
  let b : ℝ := Fintype.card Y
  have qp : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have q1 : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.one_le
  have dp : 1 ≤ K/ρ := (one_le_div hr).mpr (by linarith)
  have hp : 1 ≤ P := one_le_pow₀ dp
  have ppos := lt_of_lt_of_le zero_lt_one hp
  have ap : 0 ≤ α := by dsimp [α]; positivity
  have bp : 0 ≤ b := Nat.cast_nonneg _
  have stable (g : Law G) (hs : ∀ z, 0 < g z → ρ*b ≤ (spectrum T z).re)
      (energy : normSq g ≤ (K/ρ)^2 * normSq (diff g)) : Rectangle g T α (α*b) := by
    obtain ⟨H,z,hsize,hmass⟩ := conc g (by
      rw [← normSq_diff]
      exact (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr (by simpa [mul_comm] using energy))
    have ep : 0 < normSq g := by
      have h := one_le_card_mul_normSq g
      by_contra! hz
      linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (Fintype.card G) : 0 ≤ (Fintype.card G : ℝ)) hz]
    have size := (le_div_iff₀ ep).mp hsize
    rw [Nat.card_eq_fintype_card] at size
    have r := rectangle_of_coset g T H z P ρ ppos hr size hmass hs
    apply r.mono
    · apply div_le_div_of_nonneg_right _ qp.le
      apply (div_le_div_iff₀ (pow_pos ppos 3) ppos).mpr
      have d := mul_le_mul_of_nonneg_right (pow_le_one₀ hr.le hr1 (n := 2)) ppos.le
      have p := pow_le_pow_right₀ hp (show 1 ≤ 3 by decide)
      simpa using d.trans (by simpa using p)
    · dsimp [α,b]
      ring_nf
      exact le_rfl
  have init : cutoff 0 * Fintype.card Y ≤ ‖average f (spectrum T)‖ := by
    rw [show cutoff 0 = 1/4 by norm_num [cutoff]]
    exact bias
  obtain ⟨g,hg,hs⟩ := spectrum_step f T _ (cutoff_pos 0) init
  rw [← cutoff_succ] at hg hs
  have dom z := (mul_le_mul_of_nonneg_right
    (hrL.trans (cutoff_antitone (show 0+1 ≤ L+1 by omega))) (g.nonneg z)).trans (hg z)
  have r := stability_iteration T ρ K α (α*b) hr hr1 (by linarith) ap (mul_nonneg ap bp)
    stable L 1 g (by simpa [Nat.add_comm] using hrL) hs
    (((mul_le_mul_of_nonneg_left (normSq_le_one g) (Nat.cast_nonneg _)).trans_eq (mul_one _)).trans_lt budget)
  have lift := lift_rectangle T ρ _ _ hr.le dom r
  apply lift.mono
  · change (ρ/q)^(L+1)*α ≤ ρ*(ρ^L*α)
    rw [← mul_assoc,← pow_succ']
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (div_le_self hr.le q1) _) ap
  · change (ρ/q)^(L+1)*α*b ≤ (1/(q:ℝ))^L*(α*b)/q
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right hr1 qp.le) (L+1)) (mul_nonneg ap bp)
    rw [pow_succ] at h
    convert h using 1 <;> rw [pow_succ] <;> ring

end InducedDegreeRepetition.Duality
