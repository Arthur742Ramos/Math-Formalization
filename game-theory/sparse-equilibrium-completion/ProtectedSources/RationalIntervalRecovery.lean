/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalGapValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalIntervalRecover {k m : ℕ} (lo V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (i : Fin m) (a : Fin k) : ℚ := if q i=0 then lo i a else V i a/q i

def rationalMomentScore {k m : ℕ} (p : Fin k → ℚ) (V : Fin m → Fin k → ℚ) (i : Fin m) : ℚ :=
  ∑ a, V i a*p a

def rationalPerspectiveCall {m : ℕ} (q H : Fin m → ℚ) (ρ z : ℚ) : ℚ :=
  ∑ i, max (H i-(ρ+z)*q i) 0

theorem rational_interval_recovered_product {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    ∀ i a, q i*rationalIntervalRecover lo V q i a=V i a := by
  intro i a
  by_cases hz : q i=0
  · have hzero : V i a=0 := by
      have hbounds := hV i a
      simp only [hz,mul_zero] at hbounds
      exact le_antisymm hbounds.2 hbounds.1
    simp only [rationalIntervalRecover,hz,ite_true,zero_mul,hzero]
  · simp only [rationalIntervalRecover,hz,ite_false]
    field_simp

theorem rational_interval_recovered_bounds {k m : ℕ}
    (lo hi V : Fin m → Fin k → ℚ) (q : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    ∀ i a, lo i a ≤ rationalIntervalRecover lo V q i a ∧
      rationalIntervalRecover lo V q i a ≤ hi i a := by
  intro i a
  by_cases hz : q i=0
  · simp only [rationalIntervalRecover,hz,ite_true]
    exact ⟨le_refl _,hlu i a⟩
  · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
    simp only [rationalIntervalRecover,hz,ite_false]
    exact ⟨(le_div_iff₀ hp).mpr (hV i a).1,(div_le_iff₀ hp).mpr (hV i a).2⟩

theorem rational_recovered_score_moment {k m : ℕ}
    (lo V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (hprod : ∀ i a, q i*rationalIntervalRecover lo V q i a=V i a) :
    ∀ i, q i*rationalScore (rationalIntervalRecover lo V q) p i=rationalMomentScore p V i := by
  intro i
  unfold rationalScore rationalMomentScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [←mul_assoc,hprod i a]

theorem rational_perspective_call_identity {m : ℕ} (q t H : Fin m → ℚ) (ρ z : ℚ)
    (hq : ∀ i, 0 ≤ q i) (hH : ∀ i, q i*t i=H i) :
    rationalCall q (fun i => t i-ρ) z=rationalPerspectiveCall q H ρ z := by
  unfold rationalCall rationalPerspectiveCall
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (hq i),mul_zero]
  congr 1
  linear_combination hH i

end SparseCompletion
