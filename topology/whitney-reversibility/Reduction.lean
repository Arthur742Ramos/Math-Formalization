/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Levels
@[expose] public section
open Set Topology TopologicalSpace
universe u v
namespace WhitneyReversibility

/-- A decomposition into two proper nonempty compact connected subsets. -/
def IsDecomposable {A : Type v} [tA : TopologicalSpace A] (K : Set A) : Prop :=
  ∃ P Q : Set A, IsCompact P ∧ IsConnected P ∧ IsCompact Q ∧ IsConnected Q ∧
    P ⊆ K ∧ Q ⊆ K ∧ P ≠ K ∧ Q ≠ K ∧ P ∪ Q = K

/-- Every nondegenerate subcontinuum has a decomposition into two proper subcontinua. -/
def IsHereditarilyDecomposable {A : Type v} [tA : TopologicalSpace A] (S : Set A) : Prop :=
  ∀ K : Set A, K ⊆ S → IsCompact K → IsConnected K → K.Nontrivial → IsDecomposable K

variable {X : Type u} [mX : MetricSpace X] [cX : CompactSpace X]

def coveringCandidates (L : Set (Continuum X)) (Y : Continuum X) :
    Set (NonemptyCompacts (Continuum X)) :=
  {F | (F : Set (Continuum X)) ⊆ L ∧ IsConnected (F : Set (Continuum X)) ∧
    ∀ x ∈ (Y.val : Set X), ((F : Set (Continuum X)) ∩ {K | x ∈ (K.val : Set X)}).Nonempty}

omit [CompactSpace X] in
theorem isClosed_continuaContaining (x : X) :
    IsClosed {K : Continuum X | x ∈ (K.val : Set X)} := by
  have h : IsClosed {K : NonemptyCompacts X | x ∈ (K : Set X)} := by
    simpa only [Set.inter_singleton_nonempty] using
      NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        (isClosed_singleton : IsClosed ({x} : Set X))
  exact h.preimage (continuous_subtype_val :
    Continuous (Subtype.val : Continuum X → NonemptyCompacts X))

theorem isCompact_coveringCandidates {L : Set (Continuum X)} (hL : IsCompact L)
    (Y : Continuum X) : IsCompact (coveringCandidates L Y) := by
  have hhit : IsClosed {F : NonemptyCompacts (Continuum X) |
      ∀ x ∈ (Y.val : Set X), ((F : Set (Continuum X)) ∩ {K | x ∈ (K.val : Set X)}).Nonempty} := by
    have he : {F : NonemptyCompacts (Continuum X) |
        ∀ x ∈ (Y.val : Set X), ((F : Set (Continuum X)) ∩ {K | x ∈ (K.val : Set X)}).Nonempty} =
        ⋂ x ∈ (Y.val : Set X), {F : NonemptyCompacts (Continuum X) |
          ((F : Set (Continuum X)) ∩ {K | x ∈ (K.val : Set X)}).Nonempty} := by
      ext F
      simp only [mem_iInter, mem_ofPred_eq]
    rw [he]
    exact isClosed_biInter fun x _ =>
      NonemptyCompacts.isClosed_inter_nonempty_of_isClosed (isClosed_continuaContaining x)
  exact ((NonemptyCompacts.isClosed_subsets_of_isClosed hL.isClosed).inter
    (OrderArcs.isClosed_connected_values.inter hhit)).isCompact

omit [CompactSpace X] in
theorem candidate_union {L : Set (Continuum X)} (Y : Continuum X)
    (hLY : ∀ K ∈ L, K.val ≤ Y.val) {F : NonemptyCompacts (Continuum X)}
    (hF : F ∈ coveringCandidates L Y) : familyUnion (F : Set (Continuum X)) = (Y.val : Set X) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
    exact hLY K (hF.1 hK) hxK
  · intro x hx
    obtain ⟨K, hKF, hxK⟩ := hF.2.2 x hx
    exact mem_iUnion₂.mpr ⟨K, hKF, hxK⟩

theorem exists_minimal_covering_family {L : Set (Continuum X)} (hLc : IsCompact L)
    (hL : IsConnected L) (Y : Continuum X)
    (hLY : ∀ K ∈ L, K.val ≤ Y.val) (hunion : familyUnion L = (Y.val : Set X)) :
    ∃ S : Set (Continuum X), S ⊆ L ∧ IsCompact S ∧ IsConnected S ∧
      familyUnion S = (Y.val : Set X) ∧
      ∀ T : Set (Continuum X), T ⊆ S → IsCompact T → IsConnected T →
        familyUnion T = (Y.val : Set X) → T = S := by
  classical
  let : Nonempty (Continuum X) := ⟨Y⟩
  obtain ⟨q, hq⟩ := exists_dense_seq (Continuum X)
  let F : NonemptyCompacts (Continuum X) := ⟨⟨L, hLc⟩, hL.nonempty⟩
  have hF : F ∈ coveringCandidates L Y := by
    refine ⟨subset_rfl, hL, ?_⟩
    intro x hx
    have hx' : x ∈ familyUnion L := hunion.symm ▸ hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx'
    exact ⟨K, hK, hxK⟩
  obtain ⟨M, hM, hmin⟩ := (isCompact_coveringCandidates hLc Y).exists_isMinOn
    ⟨F, hF⟩ (OrderArcs.continuous_height q).continuousOn
  refine ⟨(M : Set (Continuum X)), hM.1, M.isCompact, hM.2.1,
    candidate_union Y hLY hM, ?_⟩
  intro T hTS hTc hTn hTu
  let N : NonemptyCompacts (Continuum X) := ⟨⟨T, hTc⟩, hTn.nonempty⟩
  have hN : N ∈ coveringCandidates L Y := by
    refine ⟨hTS.trans hM.1, hTn, ?_⟩
    intro x hx
    have hx' : x ∈ familyUnion T := hTu.symm ▸ hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx'
    exact ⟨K, hK, hxK⟩
  by_contra hne
  have hlt : N < M := lt_of_le_of_ne hTS (fun he => hne (congrArg SetLike.coe he))
  exact not_lt_of_ge (hmin hN) (OrderArcs.strictMono_height q hq hlt)

omit [CompactSpace X] in
theorem minimal_covering_family_indecomposable {L S : Set (Continuum X)} (Y : Continuum X)
    (hi : ¬ IsDecomposable (Y.val : Set X))
    (hS : S ⊆ L) (hLY : ∀ K ∈ L, K.val ≤ Y.val)
    (hunion : familyUnion S = (Y.val : Set X))
    (hmin : ∀ T : Set (Continuum X), T ⊆ S → IsCompact T → IsConnected T →
      familyUnion T = (Y.val : Set X) → T = S) : ¬ IsDecomposable S := by
  rintro ⟨P, Q, hPc, hPn, hQc, hQn, hPS, hQS, hp, hq, hPQ⟩
  apply hi
  have hPY : familyUnion P ⊆ (Y.val : Set X) := by
    intro x hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
    exact hLY K (hS (hPS hK)) hxK
  have hQY : familyUnion Q ⊆ (Y.val : Set X) := by
    intro x hx
    obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hx
    exact hLY K (hS (hQS hK)) hxK
  refine ⟨familyUnion P, familyUnion Q, isCompact_familyUnion hPc,
    isConnected_familyUnion hPn, isCompact_familyUnion hQc,
    isConnected_familyUnion hQn, hPY, hQY,
    (fun he => hp (hmin P hPS hPc hPn he)),
    (fun he => hq (hmin Q hQS hQc hQn he)), ?_⟩
  rw [← hunion, ← hPQ]
  ext x
  simp only [familyUnion, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨K, hK, hxK⟩ | ⟨K, hK, hxK⟩)
    · exact ⟨K, Or.inl hK, hxK⟩
    · exact ⟨K, Or.inr hK, hxK⟩
  · rintro ⟨K, (hK | hK), hxK⟩
    · exact Or.inl ⟨K, hK, hxK⟩
    · exact Or.inr ⟨K, hK, hxK⟩

end WhitneyReversibility
