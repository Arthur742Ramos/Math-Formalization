/- AI-assisted formalization under the repository Apache-2.0 license.
SOURCE-ONLY draft: an actual antisymmetric rational edge update.
Uncompiled while the serialized heavy verification slot belongs to topology.
This is an augmentation primitive, not a complete flow finder or runtime bound. -/
module
public import ProtectedSources.RationalNetCut
public import Mathlib.Tactic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Increase one directed net-flow entry and decrease its reverse entry.
The definition also makes sense for equal endpoints, where the update cancels. -/
def rationalNetPushEdge {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (δ : ℚ) (u v : Fin n) : ℚ :=
  F u v + (if u=a ∧ v=b then δ else 0) - (if u=b ∧ v=a then δ else 0)

theorem rational_net_push_edge_forward {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (hab : a ≠ b) (δ : ℚ) :
    rationalNetPushEdge F a b δ a b = F a b + δ := by
  simp [rationalNetPushEdge,hab,Ne.symm hab]

theorem rational_net_push_edge_backward {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (hab : a ≠ b) (δ : ℚ) :
    rationalNetPushEdge F a b δ b a = F b a - δ := by
  simp [rationalNetPushEdge,hab,Ne.symm hab]

theorem rational_net_push_edge_other {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (δ : ℚ) (u v : Fin n)
    (hforward : ¬(u=a ∧ v=b)) (hbackward : ¬(u=b ∧ v=a)) :
    rationalNetPushEdge F a b δ u v = F u v := by
  simp [rationalNetPushEdge,hforward,hbackward]

theorem rational_net_push_edge_skew {n : ℕ} (F : Fin n → Fin n → ℚ)
    (hF : ∀ u v, F u v = -F v u) (a b : Fin n) (δ : ℚ) :
    ∀ u v, rationalNetPushEdge F a b δ u v =
      -rationalNetPushEdge F a b δ v u := by
  intro u v
  simp only [rationalNetPushEdge]
  rw [hF u v]
  have hforward : (if v=a ∧ u=b then δ else 0) =
      (if u=b ∧ v=a then δ else 0) := by simp only [and_comm]
  have hbackward : (if v=b ∧ u=a then δ else 0) =
      (if u=a ∧ v=b then δ else 0) := by simp only [and_comm]
  rw [hforward,hbackward]
  ring

/-- The reverse capacity cannot be harmed by a nonnegative push. Only the
forward residual capacity is required, rather than a fictitious symmetric cap. -/
theorem rational_net_push_edge_capacity {n : ℕ}
    (C F : Fin n → Fin n → ℚ) (hF : ∀ u v, F u v ≤ C u v)
    (a b : Fin n) (hab : a ≠ b) (δ : ℚ)
    (hδ : 0 ≤ δ) (hres : δ ≤ C a b - F a b) :
    ∀ u v, rationalNetPushEdge F a b δ u v ≤ C u v := by
  intro u v
  by_cases hf : u=a ∧ v=b
  · rcases hf with ⟨hu,hv⟩
    subst u
    subst v
    rw [rational_net_push_edge_forward F a b hab δ]
    linarith
  · by_cases hb : u=b ∧ v=a
    · rcases hb with ⟨hu,hv⟩
      subst u
      subst v
      rw [rational_net_push_edge_backward F a b hab δ]
      linarith [hF b a]
    · rw [rational_net_push_edge_other F a b δ u v hf hb]
      exact hF u v

/-- Exact divergence effect of the executed edge update. This does not assume
that either endpoint is a global source or sink. -/
theorem rational_net_push_edge_divergence {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (δ : ℚ) (u : Fin n) :
    (∑ v, rationalNetPushEdge F a b δ u v) =
      (∑ v, F u v) + (if u=a then δ else 0) - (if u=b then δ else 0) := by
  simp only [rationalNetPushEdge,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have ha : (∑ v : Fin n, if u=a ∧ v=b then δ else 0) =
      (if u=a then δ else 0) := by
    by_cases h : u=a <;> simp [h]
  have hb : (∑ v : Fin n, if u=b ∧ v=a then δ else 0) =
      (if u=b then δ else 0) := by
    by_cases h : u=b <;> simp [h]
  rw [ha,hb]

theorem rational_net_push_edge_conservation_away {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (δ : ℚ) (u : Fin n) (hua : u ≠ a) (hub : u ≠ b) :
    (∑ v, rationalNetPushEdge F a b δ u v) = ∑ v, F u v := by
  rw [rational_net_push_edge_divergence]
  simp [hua,hub]

theorem rational_net_push_edge_source_value {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (hab : a ≠ b) (δ : ℚ) :
    (∑ v, rationalNetPushEdge F a b δ a v) = (∑ v, F a v) + δ := by
  rw [rational_net_push_edge_divergence]
  simp [hab]

theorem rational_net_push_edge_source_increases {n : ℕ} (F : Fin n → Fin n → ℚ)
    (a b : Fin n) (hab : a ≠ b) (δ : ℚ) (hδ : 0 < δ) :
    (∑ v, F a v) < ∑ v, rationalNetPushEdge F a b δ a v := by
  rw [rational_net_push_edge_source_value F a b hab δ]
  linarith

end SparseCompletion
