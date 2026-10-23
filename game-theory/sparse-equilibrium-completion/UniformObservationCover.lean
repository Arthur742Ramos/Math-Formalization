/- AI-assisted source-only draft under the repository Apache-2.0 license.
Exact-source verification is recorded in separate receipts. Every anchor-incident unordered pair is observed exactly,
including observed zero. The residual block has its original full interval. -/
module
public import FiniteConstraintCover
public import TwoAnchorRigidity
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Boolean adjacency for the actual two-anchor observation pattern. -/
def twoAnchorObservationEdge {ι : Type*} [DecidableEq ι]
    (a b : Fin 2 ⊕ ι) : Bool :=
  decide (a ≠ b) && match a, b with
    | .inr _, .inr _ => false
    | _, _ => true

@[simp] theorem two_anchor_observation_no_loop {ι : Type*} [DecidableEq ι]
    (a : Fin 2 ⊕ ι) : twoAnchorObservationEdge a a = false := by
  cases a <;> simp [twoAnchorObservationEdge]

theorem two_anchor_observation_symmetric {ι : Type*} [DecidableEq ι]
    (a b : Fin 2 ⊕ ι) : twoAnchorObservationEdge a b = twoAnchorObservationEdge b a := by
  cases a <;> cases b <;> simp [twoAnchorObservationEdge, ne_comm]

def twoAnchorObservedLo {ι : Type*} (K : Fin 2 → Fin 2 → ℝ)
    (D : ι → Fin 2 → ℝ) (M : ℝ) (a b : Fin 2 ⊕ ι) : ℝ :=
  match a, b with
  | .inr _, .inr _ => -M
  | _, _ => blockMatrix K D (fun _ _ => 0) a b

def twoAnchorObservedHi {ι : Type*} (K : Fin 2 → Fin 2 → ℝ)
    (D : ι → Fin 2 → ℝ) (M : ℝ) (a b : Fin 2 ⊕ ι) : ℝ :=
  match a, b with
  | .inr _, .inr _ => M
  | _, _ => blockMatrix K D (fun _ _ => 0) a b

theorem singleton_interval_constrained (M : ℝ) (hM : 0 < M) :
    ∀ v : ℝ, v ≠ -M ∨ v ≠ M := by
  intro v
  by_cases h : v = -M
  · right
    intro he
    linarith
  · exact Or.inl h

/-- Literal graph bridge: exact observed zero remains an edge. -/
theorem two_anchor_observation_edge_bridge {ι : Type*} [DecidableEq ι]
    (K : Fin 2 → Fin 2 → ℝ) (D : ι → Fin 2 → ℝ) (M : ℝ) (hM : 0 < M)
    (a b : Fin 2 ⊕ ι) :
    twoAnchorObservationEdge a b = true ↔
      intervalConstraintEdge (twoAnchorObservedLo K D M) (twoAnchorObservedHi K D M) M a b := by
  cases a <;> cases b <;>
    simp [twoAnchorObservationEdge, twoAnchorObservedLo, twoAnchorObservedHi,
      intervalConstraintEdge, singleton_interval_constrained M hM]

/-- The opposite ordered entries describe the same skew interval. -/
theorem two_anchor_observed_reverse {ι : Type*} (K : Fin 2 → Fin 2 → ℝ)
    (D : ι → Fin 2 → ℝ) (M : ℝ) (hK : IsSkew K) :
    ∀ a b : Fin 2 ⊕ ι, a ≠ b →
      twoAnchorObservedLo K D M a b = -twoAnchorObservedHi K D M b a ∧
      twoAnchorObservedHi K D M a b = -twoAnchorObservedLo K D M b a := by
  intro a b _
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact ⟨hK h h', hK h h'⟩
    | inr j => exact ⟨rfl, rfl⟩
  | inr i =>
    cases b with
    | inl h => simp [twoAnchorObservedLo, twoAnchorObservedHi, blockMatrix]
    | inr j => simp [twoAnchorObservedLo, twoAnchorObservedHi]

def twoAnchorCover {ι : Type*} [DecidableEq ι] : Finset (Fin 2 ⊕ ι) :=
  {Sum.inl 0, Sum.inl 1}

theorem two_anchor_cover_card {ι : Type*} [DecidableEq ι] :
    (twoAnchorCover (ι := ι)).card = 2 := by
  simp [twoAnchorCover]

theorem two_anchor_cover_covers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    finiteConstraintCover (twoAnchorObservationEdge (ι := ι)) twoAnchorCover := by
  intro a b hab
  cases a with
  | inl h =>
    left
    fin_cases h <;> simp [twoAnchorCover]
  | inr i =>
    cases b with
    | inl h =>
      right
      fin_cases h <;> simp [twoAnchorCover]
    | inr j => simp [twoAnchorObservationEdge] at hab

theorem card_at_least_two_of_distinct_mem {ν : Type*} [DecidableEq ν]
    (C : Finset ν) {a b : ν} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    2 ≤ C.card := by
  have hs : ({a, b} : Finset ν) ⊆ C := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha
    · have he : v = b := Finset.mem_singleton.mp hv
      subst v
      exact hb
  simpa [hab] using Finset.card_le_card hs

/-- A residual vertex and the two anchors form a constrained triangle,
so every actual cover contains at least two vertices. -/
theorem two_anchor_cover_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (C : Finset (Fin 2 ⊕ ι))
    (hC : finiteConstraintCover (twoAnchorObservationEdge (ι := ι)) C) : 2 ≤ C.card := by
  let a0 : Fin 2 ⊕ ι := .inl 0
  let a1 : Fin 2 ⊕ ι := .inl 1
  have h01 : a0 ∈ C ∨ a1 ∈ C := hC a0 a1 (by simp [twoAnchorObservationEdge, a0, a1])
  have h0j : a0 ∈ C ∨ Sum.inr j ∈ C := hC a0 (.inr j) (by simp [twoAnchorObservationEdge, a0])
  have h1j : a1 ∈ C ∨ Sum.inr j ∈ C := hC a1 (.inr j) (by simp [twoAnchorObservationEdge, a1])
  rcases h01 with h0 | h1
  · by_cases h1 : a1 ∈ C
    · exact card_at_least_two_of_distinct_mem C h0 h1 (by simp [a0, a1])
    · exact card_at_least_two_of_distinct_mem C h0 (h1j.resolve_left h1) (by simp [a0])
  · by_cases h0 : a0 ∈ C
    · exact card_at_least_two_of_distinct_mem C h0 h1 (by simp [a0, a1])
    · exact card_at_least_two_of_distinct_mem C h1 (h0j.resolve_left h0) (by simp [a1])

theorem two_anchor_observation_minimum_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := ι)) = 2 := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  apply le_antisymm
  · simpa only [two_anchor_cover_card] using
      finite_constraint_cover_minimum_le (twoAnchorObservationEdge (ι := ι)) twoAnchorCover
        two_anchor_cover_covers
  · obtain ⟨C, hC, he⟩ := finite_constraint_cover_minimum_attained
      (twoAnchorObservationEdge (ι := ι))
    rw [←he]
    exact two_anchor_cover_lower j C hC

/-- Empty residual labels leave one observed anchor edge, not a triangle. -/
theorem two_anchor_observation_minimum_empty_residual {ι : Type*} [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] :
    finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := ι)) = 1 := by
  have hc : finiteConstraintCover (twoAnchorObservationEdge (ι := ι)) {Sum.inl 0} := by
    intro a b hab
    cases a with
    | inr i => exact isEmptyElim i
    | inl h =>
      cases b with
      | inr j => exact isEmptyElim j
      | inl h' => fin_cases h <;> fin_cases h' <;> simp_all [twoAnchorObservationEdge]
  apply le_antisymm
  · simpa only [Finset.card_singleton] using
      finite_constraint_cover_minimum_le (twoAnchorObservationEdge (ι := ι)) {Sum.inl 0} hc
  · obtain ⟨C, hC, he⟩ := finite_constraint_cover_minimum_attained
      (twoAnchorObservationEdge (ι := ι))
    have hh := hC (.inl 0) (.inl 1) (by simp [twoAnchorObservationEdge])
    have hn : C.Nonempty := hh.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
    rw [←he]
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr hn)

noncomputable section

def uniformObservedLo (m : ℕ) : (Fin 2 ⊕ Fin m) → (Fin 2 ⊕ Fin m) → ℝ :=
  twoAnchorObservedLo (rigidityCore (uniformTarget m (1 / 4)))
    (rigidityCross (uniformTarget m (1 / 4))) 1

def uniformObservedHi (m : ℕ) : (Fin 2 ⊕ Fin m) → (Fin 2 ⊕ Fin m) → ℝ :=
  twoAnchorObservedHi (rigidityCore (uniformTarget m (1 / 4)))
    (rigidityCross (uniformTarget m (1 / 4))) 1

theorem uniform_observation_edge_bridge (m : ℕ) (a b : Fin 2 ⊕ Fin m) :
    twoAnchorObservationEdge a b = true ↔
      intervalConstraintEdge (uniformObservedLo m) (uniformObservedHi m) 1 a b :=
  two_anchor_observation_edge_bridge _ _ 1 (by norm_num) a b

/-- The paper's actual bounded uniform observations, not an abstract graph
chosen merely to have a prescribed cover number. -/
theorem uniform_observed_intervals_valid (m : ℕ) (hm : 0 < m) :
    ∀ a b : Fin 2 ⊕ Fin m,
      -1 ≤ uniformObservedLo m a b ∧ uniformObservedLo m a b ≤ uniformObservedHi m a b ∧
      uniformObservedHi m a b ≤ 1 := by
  have hb := two_anchor_observed_bounds hm (uniformTarget m (1 / 4))
    (fun j => le_of_lt (uniformTarget_positive m (1 / 4) (by norm_num) j))
    (uniformTarget_mass m hm (1 / 4))
  have hK : ∀ a b, -1 ≤ rigidityCore (uniformTarget m (1 / 4)) a b ∧
      rigidityCore (uniformTarget m (1 / 4)) a b ≤ 1 := by
    simpa only [rigidityCore, Nat.cast_ofNat] using hb.1
  have hD : ∀ j h, -1 ≤ rigidityCross (uniformTarget m (1 / 4)) j h ∧
      rigidityCross (uniformTarget m (1 / 4)) j h ≤ 1 := by
    simpa only [rigidityCross, Nat.cast_ofNat] using hb.2
  intro a b
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact ⟨(hK h h').1, le_refl _, (hK h h').2⟩
    | inr j =>
      have hd := hD j h
      dsimp [uniformObservedLo, uniformObservedHi, twoAnchorObservedLo, twoAnchorObservedHi, blockMatrix]
      exact ⟨by linarith, le_refl _, by linarith⟩
  | inr i =>
    cases b with
    | inl h => exact ⟨(hD i h).1, le_refl _, (hD i h).2⟩
    | inr j => norm_num [uniformObservedLo, uniformObservedHi, twoAnchorObservedLo, twoAnchorObservedHi]

/-- Actual finite-minimum computation for the nonempty-residual uniform
family. The empty-residual variant is separately one, and empty whole-label
finite graphs have minimum zero. -/
theorem uniform_constraint_cover_minimum_two (m : ℕ) (hm : 0 < m) :
    finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := Fin m)) = 2 := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact two_anchor_observation_minimum_two

/-- Original interval-cover predicate, universally over every candidate
cover set: the two anchors attain the minimum and all covers have size≥2. -/
theorem uniform_interval_cover_minimum_two (m : ℕ) (hm : 0 < m) :
    intervalVertexCover (twoAnchorCover (ι := Fin m) : Set (Fin 2 ⊕ Fin m))
      (uniformObservedLo m) (uniformObservedHi m) 1 ∧
    (twoAnchorCover (ι := Fin m)).card = 2 ∧
    ∀ (C : Set (Fin 2 ⊕ Fin m)) [DecidablePred (· ∈ C)],
      intervalVertexCover C (uniformObservedLo m) (uniformObservedHi m) 1 → 2 ≤ Fintype.card C := by
  refine ⟨?_, two_anchor_cover_card, ?_⟩
  · exact (finite_constraint_cover_interval_bridge _ _ _ 1 (uniform_observation_edge_bridge m)
      twoAnchorCover).mp two_anchor_cover_covers
  · intro C _ hC
    calc
      2 = finiteConstraintCoverMinimum (twoAnchorObservationEdge (ι := Fin m)) :=
        (uniform_constraint_cover_minimum_two m hm).symm
      _ ≤ Fintype.card C :=
        finite_constraint_cover_minimum_set_le _ _ _ 1 (uniform_observation_edge_bridge m) C hC

end
end SparseCompletion
