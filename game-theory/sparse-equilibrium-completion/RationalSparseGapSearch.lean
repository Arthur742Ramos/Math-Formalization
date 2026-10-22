/- AI-assisted formalization under the repository Apache-2.0 license.
An actual finite support search; no polynomial operation or bit-cost claim. -/
module
public import RationalSparseSupport
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseGapRun {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (z : Fin m → Fin 2) :
    Option (Fin m → ℚ) :=
  if (rationalSupportMask z).card ≤ k+rationalGridSize M r η+Fintype.card I+1 then
    rationalGapSolve K D p M r ρ η (R.append (rationalSupportZeros z)) else none

def rationalSparseGapSearch {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) : Option (Fin m → ℚ) :=
  rationalFiniteSelect (rationalGridTuples m 2)
    (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0)

theorem rational_sparse_gap_run_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (z : Fin m → Fin 2) (q : Fin m → ℚ)
    (hout : rationalSparseGapRun K D p M r ρ η R z=some q) :
    RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  unfold rationalSparseGapRun at hout
  split at hout
  next hc =>
    have h := rational_gap_solve_sound K D p M r ρ η (R.append (rationalSupportZeros z)) q hout
    have hg := (rational_gap_check_iff K D p q M r ρ η).mp h.1
    have hp := (rational_linear_append_iff _ _ q).mp h.2
    refine ⟨hg,hp.1,Nat.le_min.mpr ⟨?_,?_⟩⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (rational_support_card_of_zeros z q hg.1 hp.2) hc
  next => cases hout

theorem rational_sparse_gap_search_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ)
    (hout : rationalSparseGapSearch K D p M r ρ η R=some q) :
    RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q ∧
    (Finset.univ.filter fun i => q i ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin (rationalGridTuples m 2)
    (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0) q hout
  exact rational_sparse_gap_run_sound K D p M r ρ η R z q hz

/-- Completeness needs a real feasible finite-grid point, rather than an input
rational sparse witness or an oracle for choosing a support. -/
theorem rational_sparse_gap_search_complete {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ q, rationalSparseGapSearch K D p M r ρ η R=some q := by
  classical
  obtain ⟨y,hy,_,_,_,hc⟩ := rational_gap_real_compression K D p M r ρ η R x hx hq hm
  let z := realSupportIndex y
  have hzc : (rationalSupportMask z).card ≤ k+rationalGridSize M r η+Fintype.card I+1 := by
    rw [show z=realSupportIndex y from rfl,real_support_index_mask]
    exact le_trans hc (min_le_right _ _)
  have hzero : (rationalSupportZeros z).RealSatisfies y :=
    rational_support_zeros_real z y (fun i hi => (real_support_index_zero y i).mp hi)
  have hparts := (rational_linear_real_append_iff _ _ y).mp hy
  obtain ⟨q,hq⟩ := rational_lp_real_complete m
    ((rationalGapSystem K D p M r ρ η).append (R.append (rationalSupportZeros z)))
    ⟨y,(rational_linear_real_append_iff _ _ y).mpr
      ⟨hparts.1,(rational_linear_real_append_iff _ _ y).mpr ⟨hparts.2,hzero⟩⟩⟩
  have hrun : rationalSparseGapRun K D p M r ρ η R z=some q := by
    simpa only [rationalSparseGapRun,ite_eq_left hzc,rationalGapSolve] using hq
  cases ho : rationalSparseGapSearch K D p M r ρ η R with
  | some q => exact ⟨q,rfl⟩
  | none =>
    have hn := (rational_finite_select_none_iff (rationalGridTuples m 2)
      (rationalSparseGapRun K D p M r ρ η R) (fun _ => 0)).mp ho z
      (rational_grid_tuples_complete m 2 z)
    rw [hrun] at hn
    cases hn

end SparseCompletion
