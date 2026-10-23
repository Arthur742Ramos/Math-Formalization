/- AI-assisted formalization under the repository Apache-2.0 license.
Separate development draft. No polynomial complexity claim. -/
module
public import RationalGrid
@[expose] public section
namespace SparseCompletion

/-- Exact integer implementation of ceil(sqrt(a)). The comparison distinguishes
the perfect-square boundary that the older unconditional `sqrt(ceil(a))+1` misses. -/
def rationalCeilSqrt (a : ℚ) : ℕ :=
  let s := Nat.sqrt (Nat.ceil a)
  if a ≤ (s : ℚ)^2 then s else s+1

theorem rational_ceil_sqrt_bound (a : ℚ) :
    a ≤ (rationalCeilSqrt a : ℚ)^2 := by
  dsimp only [rationalCeilSqrt]
  split
  · assumption
  · have h := Nat.le_ceil a
    have hs : (Nat.ceil a : ℚ) < ((Nat.sqrt (Nat.ceil a)+1 : ℕ) : ℚ)^2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (Nat.ceil a)
    exact le_of_lt (lt_of_le_of_lt h hs)

theorem rational_ceil_sqrt_minimal (a : ℚ) (n : ℕ) (hn : a ≤ (n : ℚ)^2) :
    rationalCeilSqrt a ≤ n := by
  have hc : Nat.ceil a ≤ n^2 := Nat.ceil_le.mpr (by exact_mod_cast hn)
  have hs : Nat.sqrt (Nat.ceil a) ≤ n := by
    simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hc
  dsimp only [rationalCeilSqrt]
  split
  · exact hs
  · have hne : Nat.sqrt (Nat.ceil a) ≠ n := by
      intro he
      subst n
      contradiction
    omega

theorem rational_ceil_sqrt_real (a : ℚ) (ha : 0 ≤ a) :
    rationalCeilSqrt a = Nat.ceil (Real.sqrt (a : ℝ)) := by
  apply Nat.le_antisymm
  · apply rational_ceil_sqrt_minimal
    have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha)
    have hc := Nat.le_ceil (Real.sqrt (a : ℝ))
    have hh : (a : ℝ) ≤ (Nat.ceil (Real.sqrt (a : ℝ)) : ℝ)^2 := by
      nlinarith [Real.sqrt_nonneg (a : ℝ)]
    exact_mod_cast hh
  · apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_left (Nat.cast_nonneg _)).mpr
    exact_mod_cast rational_ceil_sqrt_bound a

def rationalCanonicalGridSize (M r η : ℚ) : ℕ := rationalCeilSqrt (M*r/η)

theorem rational_canonical_grid_size_real (M r η : ℚ)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (hη : 0 < η) :
    rationalCanonicalGridSize M r η = gridSize (M : ℝ) (r : ℝ) (η : ℝ) := by
  rw [rationalCanonicalGridSize, rational_ceil_sqrt_real _
    (div_nonneg (mul_nonneg hM hr) (le_of_lt hη))]
  unfold gridSize
  congr 2
  push_cast
  rfl

theorem rational_canonical_grid_size_bound (M r η : ℚ) (hη : 0 < η) :
    M*r ≤ η*(rationalCanonicalGridSize M r η : ℚ)^2 := by
  have h := (div_le_iff₀ hη).mp (rational_ceil_sqrt_bound (M*r/η))
  change M*r ≤ η*(rationalCeilSqrt (M*r/η) : ℚ)^2
  nlinarith

end SparseCompletion
