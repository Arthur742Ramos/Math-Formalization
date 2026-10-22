/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable rational residual completion through finite Fourier--Motzkin LP;
no polynomial complexity claim. -/
module
public import RationalResidualCompletion
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem residual_completion_row_count (m : ℕ) :
    Fintype.card (ResidualCompletionRows m)=4*m*m+m := by
  simp only [ResidualCompletionRows,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

theorem residual_rat_real_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) :
    ResidualRatConditions q t M σ B ↔
      ResidualRealConditions q t M σ (fun i j => (B i j : ℝ)) := by
  constructor
  · rintro ⟨hsk,hb,hr⟩
    refine ⟨?_,?_,?_⟩
    · intro i j
      change (B i j : ℝ)= -(B j i : ℝ)
      exact_mod_cast hsk i j
    · intro i j
      change -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ)
      exact_mod_cast hb i j
    · intro i
      have hi : ((t i+∑ j, B i j*q j : ℚ) : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hr i
      simpa only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul] using hi
  · rintro ⟨hsk,hb,hr⟩
    refine ⟨?_,?_,?_⟩
    · intro i j
      have hi := hsk i j
      change (B i j : ℝ)= -(B j i : ℝ) at hi
      exact_mod_cast hi
    · intro i j
      have hi := hb i j
      change -(M : ℝ) ≤ (B i j : ℝ) ∧ (B i j : ℝ) ≤ (M : ℝ) at hi
      exact_mod_cast hi
    · intro i
      have hi : ((t i+∑ j, B i j*q j : ℚ) : ℝ) ≤ (σ : ℝ) := by
        simpa only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul] using hr i
      exact_mod_cast hi

theorem residual_completion_real_exists_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    (∃ x, (residualCompletionSystem q t M σ).RealSatisfies x) ↔
      ∃ B, ResidualRealConditions q t M σ B := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨residualDecode x,(residual_completion_real_iff q t M σ x).mp hx⟩
  · rintro ⟨B,hB⟩
    refine ⟨residualEncode B,(residual_completion_real_iff q t M σ _).mpr ?_⟩
    simpa only [residual_decode_encode] using hB

/-- Total computable rational matrix reconstruction; none is genuine infeasibility.
It uses the dimension-recursive rational solver, not a flow feasibility oracle. -/
def rationalResidualCompletion {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    Option (Fin m → Fin m → ℚ) :=
  (rationalLPSolve (m*m) (residualCompletionSystem q t M σ)).map residualDecode

theorem rational_residual_completion_complete {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (h : ∃ B, ResidualRealConditions q t M σ B) :
    ∃ B, rationalResidualCompletion q t M σ=some B := by
  obtain ⟨x,hx⟩ := rational_lp_real_complete (m*m) (residualCompletionSystem q t M σ)
    ((residual_completion_real_exists_iff q t M σ).mpr h)
  exact ⟨residualDecode x,by simp only [rationalResidualCompletion,hx,Option.map_some]⟩

theorem rational_residual_completion_real_sound {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) (h : rationalResidualCompletion q t M σ=some B) :
    ResidualRealConditions q t M σ (fun i j => (B i j : ℝ)) := by
  cases hx : rationalLPSolve (m*m) (residualCompletionSystem q t M σ) with
  | none =>
    simp only [rationalResidualCompletion,hx,Option.map_none] at h
    cases h
  | some x =>
    have hB : residualDecode x=B := by
      simpa only [rationalResidualCompletion,hx,Option.map_some,Option.some.injEq] using h
    subst B
    have hr := (rational_linear_real_cast_iff (residualCompletionSystem q t M σ) x).mpr
      (rational_lp_solve_sound (m*m) (residualCompletionSystem q t M σ) x hx)
    exact (residual_completion_real_iff q t M σ (fun u => (x u : ℝ))).mp hr

theorem rational_residual_completion_rat_sound {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ)
    (B : Fin m → Fin m → ℚ) (h : rationalResidualCompletion q t M σ=some B) :
    ResidualRatConditions q t M σ B :=
  (residual_rat_real_iff q t M σ B).mpr (rational_residual_completion_real_sound q t M σ B h)

theorem rational_residual_completion_none_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    rationalResidualCompletion q t M σ=none ↔ ¬∃ B, ResidualRealConditions q t M σ B := by
  rw [rationalResidualCompletion,Option.map_eq_none_iff,rational_lp_solve_none_iff_real]
  exact not_congr (residual_completion_real_exists_iff q t M σ)

theorem rational_residual_completion_rat_iff {m : ℕ} (q t : Fin m → ℚ) (M σ : ℚ) :
    (∃ B, ResidualRatConditions q t M σ B) ↔ ∃ B, ResidualRealConditions q t M σ B := by
  constructor
  · rintro ⟨B,hB⟩
    exact ⟨fun i j => (B i j : ℝ),(residual_rat_real_iff q t M σ B).mp hB⟩
  · intro h
    obtain ⟨B,hB⟩ := rational_residual_completion_complete q t M σ h
    exact ⟨B,rational_residual_completion_rat_sound q t M σ B hB⟩

end SparseCompletion
