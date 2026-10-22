/- AI-assisted formalization under the repository Apache-2.0 license.
Sharp order for the actual attained worst-case of attained support minima.
Both lower-bound and fixed-share commitment classes, general positive M. -/
module
public import FiniteCloneLower
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem worstCaseSupport_lower (n m : ℕ) (hm : 0 < m) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
      (worstCaseSupport M (le_of_lt hM) (n+2) m (Nat.zero_lt_succ (n+1))
        η (le_of_lt hη) fixed : ℝ) := by
  have hl := finiteCloneSupportProblem_minimum_lower n m hm M η hM hη fixed
  have hb := supportProblemMinimum_le_worstCase M (le_of_lt hM) (n+2) m
    (Nat.zero_lt_succ (n+1)) η (le_of_lt hη) fixed
    (finiteCloneSupportProblem n m hm M (le_of_lt hM) fixed)
  apply le_trans hl
  exact_mod_cast hb

theorem worstCaseSupport_sharp (n m : ℕ) (hm : 0 < m) (M η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hηM : η ≤ M) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
      (worstCaseSupport M (le_of_lt hM) (n+2) m (Nat.zero_lt_succ (n+1))
        η (le_of_lt hη) fixed : ℝ) ∧
    (worstCaseSupport M (le_of_lt hM) (n+2) m (Nat.zero_lt_succ (n+1))
      η (le_of_lt hη) fixed : ℝ) ≤
      ((2 : ℕ) : ℝ)*min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) := by
  exact ⟨worstCaseSupport_lower n m hm M η hM hη fixed,
    worstCaseSupport_upper M hM (n+2) m (Nat.zero_lt_succ (n+1)) η hη hηM fixed⟩

theorem worstCaseSupport_sharp_general (k m : ℕ) (hk : (2 : ℕ) ≤ k) (hm : 0 < m)
    (M η : ℝ) (hM : 0 < M) (hη : 0 < η) (hηM : η ≤ M) (fixed : Bool) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min (k+(m : ℝ)) (k+Real.sqrt (M/η)) ≤
      (worstCaseSupport M (le_of_lt hM) k m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk)
        η (le_of_lt hη) fixed : ℝ) ∧
    (worstCaseSupport M (le_of_lt hM) k m (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk)
      η (le_of_lt hη) fixed : ℝ) ≤
      ((2 : ℕ) : ℝ)*min (k+(m : ℝ)) (k+Real.sqrt (M/η)) := by
  have he : k-2+2=k := Nat.sub_add_cancel hk
  generalize hn : k-2=n at *
  subst k
  exact worstCaseSupport_sharp n m hm M η hM hη hηM fixed

end
end SparseCompletion
