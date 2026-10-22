/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Returns actual rational strategy/payoff data; Fourier–Motzkin cost may be exponential. -/
module
public import RationalSparseGapSearch
public import RationalGapRealDecision
public import RationalResidualGap
public import RationalGapSearch
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseGapAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) :
    Option ((Fin m → ℚ) × (Fin m → Fin m → ℚ)) :=
  (rationalSparseGapSearch K D p M r ρ η R).bind (fun q =>
    (rationalResidualCompletion q (rationalScore D p) M (ρ+η)).map (fun B => (q,B)))

theorem rational_sparse_gap_algorithm_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    R.Satisfies q ∧ RationalGapConditions K D p q M r ρ η ∧
      ResidualRatConditions q (rationalScore D p) M (ρ+η) B ∧
      (Finset.univ.filter fun i => q i ≠ 0).card ≤
        min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  cases hq : rationalSparseGapSearch K D p M r ρ η R with
  | none => simp only [rationalSparseGapAlgorithm,hq,Option.bind_none] at h; cases h
  | some y =>
    cases hB : rationalResidualCompletion y (rationalScore D p) M (ρ+η) with
    | none => simp only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_none] at h; cases h
    | some C =>
      have hp : (y,C)=(q,B) := Option.some.inj (by
        simpa only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := rational_sparse_gap_search_sound K D p M r ρ η R y hq
      exact ⟨hh.2.1,hh.1,
        rational_residual_completion_rat_sound y (rationalScore D p) M (ρ+η) C hB,hh.2.2⟩

theorem rational_sparse_gap_algorithm_complete {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M) (hη : 0 < η)
    (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ q B, rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B) := by
  obtain ⟨q,hq⟩ := rational_sparse_gap_search_complete K D p M r ρ η R x hx hq hm
  have hc := rational_sparse_gap_search_sound K D p M r ρ η R q hq
  obtain ⟨B,hB⟩ := rational_gap_reconstruction_complete K D p q M r ρ η hM hη
    ((rational_gap_check_iff K D p q M r ρ η).mpr hc.1)
  change rationalResidualCompletion q (rationalScore D p) M (ρ+η)=some B at hB
  exact ⟨q,B,by simp only [rationalSparseGapAlgorithm,hq,Option.bind_some,hB,Option.map_some]⟩

end SparseCompletion
