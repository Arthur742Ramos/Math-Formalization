module

public import ErdosOverlap.Pointwise
public import Mathlib.Tactic.Linarith

/-! # Universal affine bounds for the cell integration certificate

An affine majorant of the positive part is certified by four endpoint
inequalities. This permits exact integration of every cell, including cells
that contain a zero, without assuming any unverified root location.
-/

namespace ErdosOverlap.Numerics

public section

theorem affine_nonneg_on_interval {lo hi α β x : ℝ}
    (hx : lo ≤ x ∧ x ≤ hi) (hl : 0 ≤ α*lo+β) (hh : 0 ≤ α*hi+β) :
    0 ≤ α*x+β := by
  by_cases ha : 0 ≤ α
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sub_nonneg.mpr hx.2)]

theorem positivePart_le_affine {lo hi α β x : ℝ}
    (hx : lo ≤ x ∧ x ≤ hi)
    (hl0 : 0 ≤ α*lo+β) (hlx : lo ≤ α*lo+β)
    (hh0 : 0 ≤ α*hi+β) (hhx : hi ≤ α*hi+β) :
    max x 0 ≤ α*x+β := by
  apply max_le
  · have h := affine_nonneg_on_interval (α := α-1) (β := β) hx
      (by linarith) (by linarith)
    linarith
  · exact affine_nonneg_on_interval hx hl0 hh0

theorem signed_le_abs {s x : ℝ} (hs : -1 ≤ s ∧ s ≤ 1) : s*x ≤ |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hx]
  · rw [abs_of_nonpos (le_of_not_ge hx)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ s+1) (by linarith : 0 ≤ -x)]

theorem unit_mul_le_positivePart {s x : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) :
    s*x ≤ max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hx]
  · rw [max_eq_right (le_of_not_ge hx)]
    exact mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge hx)

theorem abs_sub_positivePart (x : ℝ) : |x|-max x 0 = max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hn := le_of_not_ge hx
    rw [abs_of_nonpos hn, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

/-- A universal affine minorant of the exact scalar conjugate. The two
positive-part majorants are instantiated by finite checked endpoint data. -/
theorem conjugate_affine_minorant
    {A B L U lam s t ρ σ α₁ β₁ α₂ β₂ : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hσ : 0 ≤ σ ∧ σ ≤ 1)
    (h₁ : max (|lam|-s*A+σ*B) 0 ≤ α₁*(|lam|-s*A+σ*B)+β₁)
    (h₂ : max (|lam|-s*A-t*B) 0 ≤ α₂*(|lam|-s*A-t*B)+β₂) :
    ρ*B*L - min U L*(α₁*(|lam|-s*A+σ*B)+β₁) -
      (U-min U L)*(α₂*(|lam|-s*A-t*B)+β₂) ≤
      profileConjugate (max B 0) (|A|+|B|) L U lam := by
  have hK : 0 ≤ min U L := le_min hU hL
  have hV : 0 ≤ U-min U L := sub_nonneg.mpr (min_le_left _ _)
  have hsA := signed_le_abs (x := A) hs
  have htB := signed_le_abs (x := B) ht
  have hrB := unit_mul_le_positivePart (x := B) hρ
  have hnB := unit_mul_le_positivePart (x := -B) hσ
  have hb := abs_sub_positivePart B
  have hg₁ : |lam|-(|A|+|B|)+max B 0 ≤ |lam|-s*A+σ*B := by
    nlinarith
  have hg₂ : |lam|-(|A|+|B|) ≤ |lam|-s*A-t*B := by linarith
  have hm₁ := (max_le_max_right 0 hg₁).trans h₁
  have hm₂ := (max_le_max_right 0 hg₂).trans h₂
  have hp₁ := mul_le_mul_of_nonneg_left hm₁ hK
  have hp₂ := mul_le_mul_of_nonneg_left hm₂ hV
  have hp₀ := mul_le_mul_of_nonneg_right hrB hL
  unfold profileConjugate
  linarith

end
end ErdosOverlap.Numerics
