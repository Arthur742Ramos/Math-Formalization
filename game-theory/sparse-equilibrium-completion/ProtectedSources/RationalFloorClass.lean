/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorGridAccuracy
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

abbrev FloorIntervalGameData (k m : ℕ) := (Fin k → ℝ) × IntervalGameData k m

def floorIntervalGameBox {k m : ℕ} {I : Type*} (d : RationalIntervalParameters k m I) :
    Set (FloorIntervalGameData k m) :=
  Set.Icc (fun _ => 0) (fun _ => 1) ×ˢ
    (Set.Icc (fun _ => 0) (fun _ => 1) ×ˢ
      (Set.Icc (fun i a => (d.lo i a : ℝ)) (fun i a => (d.hi i a : ℝ)) ×ˢ
        (Set.Icc (fun a b => (d.loK a b : ℝ)) (fun a b => (d.hiK a b : ℝ)) ×ˢ skewBox d.M)))

def floorIntervalGameClass {k m : ℕ} {I : Type*} (d : RationalIntervalParameters k m I)
    (s : Fin k → ℚ) (u : Fin m → ℚ) : Set (FloorIntervalGameData k m) :=
  floorIntervalGameBox d ∩ {z | (∀ a,(s a : ℝ) ≤ z.1 a) ∧
    (∀ i,(u i : ℝ) ≤ z.2.1 i) ∧ (∑ a,z.1 a)+(∑ i,z.2.1 i)=1 ∧ IsSkew z.2.2.2.1}

theorem floor_interval_game_class_compact {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ) :
    IsCompact (floorIntervalGameClass d s u) := by
  have hc : IsCompact (floorIntervalGameBox d) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod (skewBox_compact d.M))))
  apply hc.inter_right
  have he : {z : FloorIntervalGameData k m | (∀ a,(s a : ℝ) ≤ z.1 a) ∧
      (∀ i,(u i : ℝ) ≤ z.2.1 i) ∧ (∑ a,z.1 a)+(∑ i,z.2.1 i)=1 ∧ IsSkew z.2.2.2.1}=
      (⋂ a,{z | (s a : ℝ) ≤ z.1 a}) ∩ ((⋂ i,{z | (u i : ℝ) ≤ z.2.1 i}) ∩
        ({z | (∑ a,z.1 a)+(∑ i,z.2.1 i)=1} ∩
          (⋂ a,⋂ b,{z | z.2.2.2.1 a b= -z.2.2.2.1 b a}))) := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,IsSkew]
  rw [he]
  exact (isClosed_iInter fun a => isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq (by fun_prop) (by fun_prop))))

def floorIntervalGameExploitability {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (z : FloorIntervalGameData k m) : ℝ :=
  exploitability (intervalGameMatrix z.2) (blockWeights z.1 z.2.1)

theorem floor_interval_game_exploitability_continuous {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)] :
    Continuous (floorIntervalGameExploitability (k := k) (m := m)) := by
  unfold floorIntervalGameExploitability intervalGameMatrix exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl a => simp only [block_response_anchor,anchorResponse]; fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

def floorIntervalGameValue {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ) : ℝ :=
  sInf (floorIntervalGameExploitability '' floorIntervalGameClass d s u)

theorem floor_interval_game_value_attained {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hne : (floorIntervalGameClass d s u).Nonempty) :
    ∃ z ∈ floorIntervalGameClass d s u,
      floorIntervalGameExploitability z=floorIntervalGameValue d s u := by
  have hc := (floor_interval_game_class_compact d s u).image floor_interval_game_exploitability_continuous
  obtain ⟨v,hv,he⟩ := hc.sInf_mem (hne.image floorIntervalGameExploitability)
  exact ⟨v,hv,he⟩

end
end SparseCompletion
