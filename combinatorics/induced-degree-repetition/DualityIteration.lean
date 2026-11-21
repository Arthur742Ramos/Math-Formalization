module

public import DualityRectangle
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

/-- The character-bias cutoff after i rounds. -/
@[expose] noncomputable def cutoff (i : ℕ) : ℝ := 2*(1/8 : ℝ)^(2^i)
theorem cutoff_succ (i : ℕ) : cutoff (i+1) = (cutoff i)^2/2 := by
  simp only [cutoff,pow_succ 2 i,pow_mul]
  ring
theorem cutoff_pos (i : ℕ) : 0 < cutoff i := by unfold cutoff; positivity
theorem cutoff_antitone : Antitone cutoff := by
  intro i j h
  unfold cutoff
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.pow_le_pow_right (by decide) h)

/-- If the difference energy is small, conditioning still decreases the original
energy by a factor of K. -/
theorem energy_drop (f g : Law G) (ρ K : ℝ) (hr : 0 < ρ) (hk : 1 ≤ K)
    (dom : ∀ z, ρ * g z ≤ diff f z)
    (fast : (K/ρ)^2 * normSq (diff f) < normSq f) : K * normSq g < normSq f := by
  have bound : ρ^2 * normSq g ≤ normSq (diff f) := by
    unfold normSq
    rw [mul_sum]
    exact sum_le_sum fun z _ => by
      rw [← mul_pow]
      exact (sq_le_sq₀ (mul_nonneg hr.le (g.nonneg z)) (diff_nonneg f z)).mpr (dom z)
  have h := (mul_le_mul_of_nonneg_left bound (sq_nonneg (K/ρ))).trans_lt fast
  have e : (K/ρ)^2*(ρ^2*normSq g) = K^2*normSq g := by field_simp
  rw [e] at h
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K^2)
    (sum_nonneg fun _ _ => sq_nonneg _)) h

theorem stability_iteration (T : Y → G →+ ZMod q) (ρ K a b : ℝ) (hr : 0 < ρ)
    (hr1 : ρ ≤ 1) (hk : 1 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (stable : ∀ f : Law G, (∀ z, 0 < f z → ρ * Fintype.card Y ≤ (spectrum T z).re) →
      normSq f ≤ (K/ρ)^2 * normSq (diff f) → Rectangle f T a b) (k i : ℕ) (f : Law G)
    (room : ρ ≤ cutoff (i+k))
    (support : ∀ z, 0 < f z → cutoff i * Fintype.card Y ≤ (spectrum T z).re)
    (budget : Fintype.card G * normSq f < K^k) :
    Rectangle f T (ρ^k*a) ((1/(q:ℝ))^k*b) := by
  induction k generalizing i f with
  | zero =>
    exfalso
    exact (not_lt_of_ge (one_le_card_mul_normSq f)) (by simpa using budget)
  | succ k ih =>
    have now := room.trans (cutoff_antitone (show i ≤ i+(k+1) by omega))
    by_cases slow : normSq f ≤ (K/ρ)^2 * normSq (diff f)
    · have r := stable f (fun z hz => (mul_le_mul_of_nonneg_right now (Nat.cast_nonneg _)).trans (support z hz)) slow
      apply r.mono
      · exact mul_le_of_le_one_left ha (pow_le_one₀ hr.le hr1)
      · apply mul_le_of_le_one_left hb
        apply pow_le_one₀ (by positivity)
        exact (div_le_one (by exact_mod_cast NeZero.pos q)).mpr (by exact_mod_cast NeZero.one_le)
    · have bias := bias_of_support f T _ support
      obtain ⟨g,hg,hs⟩ := spectrum_step f T _ (cutoff_pos i) bias
      rw [← cutoff_succ] at hg hs
      have next := room.trans (cutoff_antitone (show i+1 ≤ i+(k+1) by omega))
      have dom z := (mul_le_mul_of_nonneg_right next (g.nonneg z)).trans (hg z)
      have drop := energy_drop f g ρ K hr hk dom (lt_of_not_ge slow)
      have bp : (Fintype.card G : ℝ) * normSq g < K^k := by
        apply lt_of_mul_lt_mul_right (a := K) _ (by linarith)
        calc
          _ = (Fintype.card G : ℝ) * (K * normSq g) := by ring
          _ ≤ (Fintype.card G : ℝ) * normSq f := mul_le_mul_of_nonneg_left drop.le (Nat.cast_nonneg _)
          _ < _ := by simpa [pow_succ] using budget
      have r := ih (i+1) g (by simpa only [Nat.add_assoc,Nat.add_comm 1 k] using room) hs bp
      have lift := lift_rectangle T ρ _ _ hr.le dom r
      convert lift using 1 <;> rw [pow_succ] <;> ring

end InducedDegreeRepetition.Duality
