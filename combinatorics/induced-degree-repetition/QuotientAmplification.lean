module

public import CosetProjection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Uniform atom bound after i differences on every quotient losing at most the
given logarithmic amount of group order. -/
@[expose] def quotientBound (f : Law G) (i : ℕ) (a B r : ℝ) : Prop :=
  ∀ (K : Type) [AddCommGroup K] [Fintype K] (p : G →+ K), Function.Surjective p →
    (Fintype.card G:ℝ) ≤ Fintype.card K*Real.exp (B*r) →
    ∀ z, ((f.push p).iter i) z ≤ Real.exp (-a*r)

theorem quotient_base (f : Law G) (a B r : ℝ)
    (hm : ∀ (H : AddSubgroup G), (Nat.card H:ℝ) ≤ Real.exp (B*r) →
      ∀ z, massOn f {x | x-z ∈ H} ≤ Real.exp (-a*r)) : quotientBound f 0 a B r := by
  intro K ga kf p sur cost z
  apply Law.push_atom_of_cosets f p _ (Real.exp_pos _).le _ z
  apply hm
  have eq := Law.card_domain p sur
  have e : (Fintype.card G:ℝ) = (Nat.card p.ker:ℝ)*Fintype.card K := by
    exact_mod_cast (by simpa [Nat.card_eq_fintype_card] using eq : Fintype.card G = Nat.card p.ker*Fintype.card K)
  apply le_of_mul_le_mul_right (a := (Fintype.card K:ℝ)) _ (by exact_mod_cast Fintype.card_pos)
  rw [← e,mul_comm]
  exact cost

theorem quotient_once (f : Law G) (i : ℕ) (a B r : ℝ) (h : quotientBound f i a B r) :
    quotientBound f (i+1) a B r := by
  intro K ga kf p sur cost z
  exact (Law.difference_le _ _).trans (Law.normSq_le_atom_bound _ _ (h K p sur cost))

theorem quotient_weaken (f : Law G) (i : ℕ) (a B b r : ℝ) (hr : 0 ≤ r)
    (hB : b ≤ B) (h : quotientBound f i a B r) : quotientBound f i a b r := by
  intro K ga kf p sur cost
  apply h K p sur
  exact cost.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB hr)) (Nat.cast_nonneg _))

/-- A failed improvement at level i+2 forces a heavy coset at level i. Pushing
to its quotient brings that coset inside the preceding atom bound. -/
theorem amplify_step (f : Law G) {q C : ℕ} (tor : ∀ x : G, q • x = 0)
    (conc : ∀ {K : Type} [AddCommGroup K] [Fintype K], (∀ x : K, q • x = 0) →
      ∀ g : Law K, ∀ d : ℝ, 2 ≤ d → normSq g/d^2 ≤ normSq (convolution g g) →
        ∃ (H : AddSubgroup K) (z : K), (Nat.card H:ℝ) ≤ d^C/normSq g ∧ 1/d^C ≤ massOn g {x | x-z ∈ H})
    (i : ℕ) (a b next B v r : ℝ) (hr : 0 < r) (large : 2 ≤ Real.exp (v*r))
    (gap : next ≤ b+2*v) (gain : C*v < a)
    (prev : quotientBound f i a (B+next+C*v) r) (mid : quotientBound f (i+1) b B r) :
    quotientBound f (i+2) next B r := by
  classical
  intro K ga kf p sur cost z
  let σ := (f.push p).iter i
  let d := Real.exp (v*r)
  have dp : 0 < d := Real.exp_pos _
  have dc : d^C = Real.exp ((C:ℝ)*v*r) := by dsimp [d]; rw [← Real.exp_nat_mul]; congr 1; ring
  by_contra! fail
  have late : Real.exp (-next*r) < normSq σ.difference :=
    fail.trans_le (Law.difference_le _ _)
  have early : Real.exp (-next*r) < normSq σ := late.trans_le (Law.iter_antitone (f.push p) i)
  have up : normSq σ ≤ Real.exp (-b*r) := by
    rw [show normSq σ = ((f.push p).iter (i+1)) 0 from (Law.iter_zero ..).symm]
    exact mid K p sur cost 0
  have e : normSq σ / d^2 ≤ normSq (convolution σ σ) := by
    rw [← normSq_diff]
    apply le_trans (div_le_div_of_nonneg_right up (sq_nonneg d)) _
    apply le_trans _ late.le
    dsimp [d]
    rw [← Real.exp_nat_mul,← Real.exp_sub,Real.exp_le_exp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right gap hr.le]
  have tk (x : K) : q • x = 0 := by obtain ⟨g,rfl⟩ := sur x; rw [← map_nsmul,tor,map_zero]
  obtain ⟨H,z',hs,hm⟩ := conc tk σ d large e
  have ep : 0 < normSq σ := (Real.exp_pos _).trans early
  have size : (Nat.card H:ℝ) ≤ Real.exp ((next+C*v)*r) := by
    apply hs.trans
    rw [dc,div_le_iff₀ ep]
    calc
      _ = Real.exp ((next+(C:ℝ)*v)*r)*Real.exp (-next*r) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left early.le (Real.exp_pos _).le
  let π := QuotientAddGroup.mk' H
  let s := π.comp p
  have more : (Fintype.card G:ℝ) ≤ Fintype.card (K ⧸ H)*Real.exp ((B+next+C*v)*r) := by
    apply cost.trans
    rw [Law.card_quotient H]
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left size (Nat.cast_nonneg (Fintype.card (K ⧸ H)): (0:ℝ)≤Fintype.card (K ⧸ H))) (Real.exp_pos (B*r)).le
    apply h.trans
    rw [mul_assoc,← Real.exp_add]
    apply le_of_eq; congr 2; ring
  have upper := prev (K ⧸ H) s ((QuotientAddGroup.mk'_surjective H).comp sur) more (π z')
  have eq : ((f.push s).iter i) = σ.push π := by
    rw [Law.push_iter,Law.push_comp]
    rfl
  rw [eq,← Law.quotient_mass] at upper
  rw [dc,one_div,← Real.exp_neg] at hm
  exact (not_le_of_gt (Real.exp_lt_exp.mpr (by nlinarith [mul_lt_mul_of_pos_right gain hr] :
    -a*r < -((C:ℝ)*v*r)))) (hm.trans upper)

end InducedDegreeRepetition.Duality
