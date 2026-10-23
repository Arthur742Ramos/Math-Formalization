/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalGrid
@[expose] public section
namespace SparseCompletion

theorem rational_grid_size_positive (M r η : ℚ) : 0 < rationalGridSize M r η := by
  unfold rationalGridSize
  omega

theorem rational_grid_size_linear_bound (M r η : ℚ) :
    rationalGridSize M r η ≤ Nat.ceil (M*r/η)+1 :=
  Nat.add_le_add_right (Nat.sqrt_le_self _) 1

theorem rational_grid_size_sqrt_bound (M r η : ℚ)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hη : 0 < η) :
    (rationalGridSize M r η : ℝ) ≤
      Real.sqrt ((M : ℝ)*(r : ℝ)/(η : ℝ))+(2 : ℕ) := by
  let a := M*r/η
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hM hr) (le_of_lt hη)
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hceil : (Nat.ceil a : ℝ) < (a : ℝ)+1 := by exact_mod_cast Nat.ceil_lt_add_one ha
  have hs : (Nat.sqrt (Nat.ceil a) : ℝ)^2 ≤ (Nat.ceil a : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (Nat.ceil a)
  have hroot := Real.sq_sqrt haR
  have hroot0 := Real.sqrt_nonneg (a : ℝ)
  have hn : (0 : ℝ) ≤ (Nat.sqrt (Nat.ceil a) : ℝ) := Nat.cast_nonneg _
  have hh : (Nat.sqrt (Nat.ceil a) : ℝ) ≤ Real.sqrt (a : ℝ)+1 := by nlinarith
  have he : (a : ℝ)=(M : ℝ)*(r : ℝ)/(η : ℝ) := by dsimp only [a]; push_cast; rfl
  unfold rationalGridSize
  change ((Nat.sqrt (Nat.ceil a)+1 : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add,Nat.cast_one,←he]
  norm_num only [Nat.cast_ofNat]
  linarith

end SparseCompletion
