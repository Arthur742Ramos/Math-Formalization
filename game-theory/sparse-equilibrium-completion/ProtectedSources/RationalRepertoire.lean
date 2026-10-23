/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalGapRealDecision
public import ProtectedSources.ValueBounds
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalRealRepertoire {I : Type*} {m : ℕ} (R : RationalLinearSystem I m) (r : ℚ) :
    Set (Fin m → ℝ) := {x | R.RealSatisfies x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=(r : ℝ)}

theorem rational_real_repertoire_closed {I : Type*} {m : ℕ}
    (R : RationalLinearSystem I m) (r : ℚ) : IsClosed (rationalRealRepertoire R r) := by
  have he : rationalRealRepertoire R r=
      (⋂ i, {x : Fin m → ℝ | (∑ j, (R.coefficient i j : ℝ)*x j) ≤ (R.rightSide i : ℝ)}) ∩
      ((⋂ j, {x | (0 : ℝ) ≤ x j}) ∩ {x | (∑ j, x j)=(r : ℝ)}) := by
    ext x
    simp only [rationalRealRepertoire,RationalLinearSystem.RealSatisfies,Set.mem_ofPred_eq,
      Set.mem_inter_iff,Set.mem_iInter]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_eq (by fun_prop) continuous_const))

theorem rational_real_repertoire_compact {I : Type*} {m : ℕ}
    (R : RationalLinearSystem I m) (r : ℚ) : IsCompact (rationalRealRepertoire R r) := by
  have hc := rational_real_repertoire_closed R r
  apply (show IsCompact (Set.Icc (fun _ : Fin m => (0 : ℝ)) (fun _ => (r : ℝ))) from isCompact_Icc).of_isClosed_subset hc
  intro x hx
  refine ⟨hx.2.1,?_⟩
  intro i
  have hh := Finset.single_le_sum (fun j (_h : j ∈ (Finset.univ : Finset (Fin m))) => hx.2.1 j)
    (Finset.mem_univ i)
  rwa [hx.2.2] at hh

end SparseCompletion
