/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalClass
public import ProtectedSources.ValueBounds
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalGameMatrix {k m : ℕ} (z : IntervalGameData k m) :
    (Fin k ⊕ Fin m) → (Fin k ⊕ Fin m) → ℝ := blockMatrix z.2.2.1 z.2.1 z.2.2.2

def intervalGameWeights {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (z : IntervalGameData k m) : (Fin k ⊕ Fin m) → ℝ :=
  blockWeights (fun a => (d.p a : ℝ)) z.1

def intervalGameExploitability {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) : ℝ :=
  exploitability (intervalGameMatrix z) (intervalGameWeights d z)

theorem interval_game_exploitability_continuous {k m : ℕ} {I : Type*}
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) :
    Continuous (intervalGameExploitability d) := by
  unfold intervalGameExploitability intervalGameMatrix intervalGameWeights exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl a =>
    simp only [block_response_anchor,anchorResponse]
    fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

def intervalGameValue {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) : ℝ :=
  sInf (intervalGameExploitability d '' intervalGameClass d)

theorem interval_game_value_attained {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) :
    ∃ z ∈ intervalGameClass d, intervalGameExploitability d z=intervalGameValue d := by
  have hc := (interval_game_class_compact d).image (interval_game_exploitability_continuous d)
  have hn := (interval_game_class_nonempty d).image (intervalGameExploitability d)
  obtain ⟨z,hz,he⟩ := hc.sInf_mem hn
  exact ⟨z,hz,he⟩

theorem interval_game_value_le_witness {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass d) :
    intervalGameValue d ≤ intervalGameExploitability d z := by
  apply csInf_le ((interval_game_class_compact d).image
    (interval_game_exploitability_continuous d)).bddBelow
  exact ⟨z,hz,rfl⟩

theorem interval_game_class_game_facts {k m : ℕ} {I : Type*}
    (d : RationalIntervalModel k m I) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass d) :
    (∀ a, 0 ≤ intervalGameWeights d z a) ∧ (∑ a, intervalGameWeights d z a)=1 ∧
    IsSkew (intervalGameMatrix z) ∧
    (∀ a b, -(d.M : ℝ) ≤ intervalGameMatrix z a b ∧ intervalGameMatrix z a b ≤ (d.M : ℝ)) := by
  rcases hz with ⟨⟨⟨hq,_⟩,⟨hDl,hDu⟩,⟨hKl,hKu⟩,hB,hBb⟩,hm,hK,_⟩
  have hKb : ∀ a b, -(d.M : ℝ) ≤ z.2.2.1 a b ∧ z.2.2.1 a b ≤ (d.M : ℝ) := by
    intro a b
    exact ⟨le_trans (by change -(d.M : ℝ) ≤ (d.loK a b : ℝ); exact_mod_cast d.coreLower a b) (hKl a b),
      le_trans (hKu a b) (by change (d.hiK a b : ℝ) ≤ (d.M : ℝ); exact_mod_cast d.coreUpper a b)⟩
  have hDb : ∀ i a, -(d.M : ℝ) ≤ z.2.1 i a ∧ z.2.1 i a ≤ (d.M : ℝ) := by
    intro i a
    exact ⟨le_trans (by change -(d.M : ℝ) ≤ (d.lo i a : ℝ); exact_mod_cast d.crossLower i a) (hDl i a),
      le_trans (hDu i a) (by change (d.hi i a : ℝ) ≤ (d.M : ℝ); exact_mod_cast d.crossUpper i a)⟩
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast d.anchorNonneg a) hq,?_,
    blockMatrix_skew _ _ _ hK hB,blockMatrix_bounds _ _ _ _ hKb hDb hBb⟩
  change (∑ a, blockWeights (fun a => (d.p a : ℝ)) z.1 a)=1
  rw [blockWeights_mass,hm]
  exact_mod_cast d.normalized

theorem interval_game_value_bounds {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalModel k m I) : 0 ≤ intervalGameValue d ∧ intervalGameValue d ≤ (d.M : ℝ) := by
  obtain ⟨z,hz,he⟩ := interval_game_value_attained d
  obtain ⟨hq,hm,hK,hb⟩ := interval_game_class_game_facts d z hz
  rw [←he]
  exact ⟨exploitability_nonnegative _ _ hK hq hm,
    exploitability_bounded_above _ _ _ (fun a b => (hb a b).2) hq hm⟩

end
end SparseCompletion
