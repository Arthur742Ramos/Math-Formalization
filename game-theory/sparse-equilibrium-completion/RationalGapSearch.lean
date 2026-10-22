/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Uses verified rational elimination; no polynomial-time or bit-cost assertion. -/
module
public import RationalGapDecision
public import Bisection
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_shifted_call_antitone {I : Type*} [Fintype I]
    (q t : I → ℚ) (ρ ρ' z : ℚ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    rationalCall q (fun i => t i-ρ') z ≤ rationalCall q (fun i => t i-ρ) z := by
  unfold rationalCall
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) (le_refl 0)) (hq i)

theorem rational_gap_conditions_monotone {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ ρ' η : ℚ) (hρ : ρ ≤ ρ') (h : RationalGapConditions K D p q M r ρ η) :
    RationalGapConditions K D p q M r ρ' η := by
  rcases h with ⟨hq,hm,hg,ha,hc⟩
  refine ⟨hq,hm,fun i => by linarith [hg i],fun a => le_trans (ha a) hρ,?_⟩
  intro l
  exact le_trans (rational_shifted_call_antitone q (rationalScore D p) ρ ρ' _ hq hρ) (hc l)

def RationalGapExists {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Prop :=
  ∃ q, RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q

instance rationalGapExistsDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Decidable (RationalGapExists K D p M r ρ η R) :=
  match he : rationalGapSolve K D p M r ρ η R with
  | none => isFalse ((rational_gap_solve_none_iff K D p M r ρ η R).mp he)
  | some q => isTrue ⟨q,(rational_gap_check_iff K D p q M r ρ η).mp
      (rational_gap_solve_sound K D p M r ρ η R q he).1,
      (rational_gap_solve_sound K D p M r ρ η R q he).2⟩

theorem rational_gap_exists_monotone {k m : ℕ} {I : Type*}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r η : ℚ)
    (R : RationalLinearSystem I m) : Monotone (fun ρ => RationalGapExists K D p M r ρ η R) := by
  intro ρ ρ' hρ
  rintro ⟨q,hq,hR⟩
  exact ⟨q,rational_gap_conditions_monotone K D p q M r ρ ρ' η hρ hq,hR⟩

def rationalGapSearch {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I m) (n : ℕ) : ℚ × ℚ :=
  RationalBisection.search (fun ρ => RationalGapExists K D p M r ρ η R) n 0 M

theorem rational_gap_search_bracket {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I m) (n : ℕ) (hM : 0 ≤ M)
    (hupper : RationalGapExists K D p M r M η R) :
    let z := rationalGapSearch K D p M r η R n
    0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ M ∧ RationalGapExists K D p M r z.2 η R ∧
      (z.1=0 ∨ ¬RationalGapExists K D p M r z.1 η R) ∧
      z.2-z.1 ≤ M/((2 : ℕ) : ℚ)^n := by
  simpa only [rationalGapSearch,sub_zero] using
    RationalBisection.search_spec (fun ρ => RationalGapExists K D p M r ρ η R) n 0 M hM hupper

end SparseCompletion
