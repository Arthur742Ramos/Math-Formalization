module

public import QuotientAmplification
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset Filter
open scoped Classical Topology

@[expose] noncomputable def levelRate (a κ : ℝ) (i : ℕ) := a*(1+κ)^(i/2)

theorem all_level_bounds (q : ℕ) (hq : 2 ≤ q) (a : ℝ) (ha : 0 < a) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (i : ℕ) (B : ℝ), 0 < B →
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ r : ℕ in atTop,
        ∀ (G : Type) [Fintype G] [AddCommGroup G], (∀ x : G, q • x = 0) →
        ∀ f : Law G, (∀ H : AddSubgroup G, (Nat.card H:ℝ) ≤ Real.exp (D*r) →
          ∀ z, massOn f {x | x-z ∈ H} ≤ Real.exp (-a*r)) →
        quotientBound f i (levelRate a κ i) B r := by
  obtain ⟨C,concentrate⟩ := coset_concentration q hq
  let κ : ℝ := 1/(2*(C+1))
  have kp : 0 < κ := by dsimp [κ]; positivity
  have kC : (C:ℝ)*κ < 1 := by
    dsimp [κ]
    rw [mul_one_div,div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg C : 0 ≤ (C:ℝ))]
  have ap (i : ℕ) : 0 < levelRate a κ i := by dsimp [levelRate]; positivity
  refine ⟨κ,kp,?_⟩
  intro i
  induction i using Nat.twoStepInduction with
  | zero =>
    intro B hp
    exact ⟨B,hp,Eventually.of_forall fun r G _ _ _ f h => by simpa [levelRate] using quotient_base f a B r h⟩
  | one =>
    intro B hp
    exact ⟨B,hp,Eventually.of_forall fun r G _ _ _ f h =>
      quotient_once f 0 _ B r (by simpa [levelRate] using quotient_base f a B r h)⟩
  | more i hi hj =>
    intro B hp
    let A := levelRate a κ i
    let next := levelRate a κ (i+2)
    let v := A*κ
    have vp : 0 < v := mul_pos (ap i) kp
    have nextEq : next = A*(1+κ) := by
      dsimp [next,A,levelRate]
      rw [show (i+2)/2 = i/2+1 by omega,pow_succ,mul_assoc]
    have mono : A ≤ levelRate a κ (i+1) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀
      (by linarith : 1 ≤ 1+κ) (show i/2 ≤ (i+1)/2 by omega)) ha.le
    have gap : next ≤ levelRate a κ (i+1)+2*v := by rw [nextEq]; dsimp [v]; nlinarith [mul_pos (ap i) kp]
    have gain : (C:ℝ)*v < A := by dsimp [v]; nlinarith [mul_lt_mul_of_pos_right kC (ap i)]
    obtain ⟨D₁,dp₁,h₁⟩ := hi (B+next+C*v) (by have := ap (i+2); dsimp [next]; positivity)
    obtain ⟨D₂,dp₂,h₂⟩ := hj B hp
    obtain ⟨r₀,hr₀⟩ := exists_nat_gt (Real.log 2/v)
    refine ⟨max D₁ D₂,dp₁.trans_le (le_max_left ..),?_⟩
    filter_upwards [h₁,h₂,eventually_ge_atTop r₀,eventually_ge_atTop 1] with r h₁ h₂ h₀ hr
    intro G fg ga tor f hm
    have rp : (0:ℝ) < r := by exact_mod_cast hr
    have h v' (hv : v' ≤ max D₁ D₂) (H : AddSubgroup G) (small : (Nat.card H:ℝ) ≤ Real.exp (v'*r)) :=
      hm H (small.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hv rp.le)))
    apply amplify_step f tor (C := C) (fun tt g d hD => concentrate tt g.val g.nonneg g.total d hD)
      i A (levelRate a κ (i+1)) next B v r rp _ gap gain (h₁ G tor f (h _ (le_max_left ..))) (h₂ G tor f (h _ (le_max_right ..)))
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    have := (div_lt_iff₀ vp).mp (hr₀.trans_le (by exact_mod_cast h₀ : (r₀:ℝ) ≤ r))
    linarith

end InducedDegreeRepetition.Duality
