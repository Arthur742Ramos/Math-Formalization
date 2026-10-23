/- AI-assisted source-only draft under the repository Apache-2.0 license.
Exact-source verification is recorded in separate receipts. The finite minimum below is computed from all actual
finite vertex subsets; no minimum-cover property is supplied as an input. -/
module
public import ProtectedSources.ObservationCover
public import ProtectedSources.CoverRelabel
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
@[expose] public section
namespace SparseCompletion

/-- A concrete finite Boolean graph cover. Symmetry is not needed by the
finite minimum algorithm; semantic graph bridges establish it where required. -/
def finiteConstraintCover {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) (C : Finset ν) : Prop :=
  ∀ a b, edge a b = true → a ∈ C ∨ b ∈ C

instance finiteConstraintCoverDecidable {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) (C : Finset ν) : Decidable (finiteConstraintCover edge C) :=
  inferInstanceAs (Decidable (∀ a b, edge a b = true → a ∈ C ∨ b ∈ C))

/-- All cardinalities of actual finite vertex covers, obtained by exhaustive
finite-subset enumeration. No graph-algorithm efficiency bound is asserted. -/
def finiteConstraintCoverSizes {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) : Finset ℕ :=
  ((Finset.univ.powerset).filter (finiteConstraintCover edge)).image Finset.card

theorem finite_constraint_cover_univ {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) : finiteConstraintCover edge Finset.univ := by
  intro a b _
  exact Or.inl (Finset.mem_univ a)

theorem finite_constraint_cover_sizes_nonempty {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) : (finiteConstraintCoverSizes edge).Nonempty := by
  refine ⟨Finset.univ.card, Finset.mem_image.mpr ⟨Finset.univ, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), finite_constraint_cover_univ edge⟩

def finiteConstraintCoverMinimum {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) : ℕ :=
  (finiteConstraintCoverSizes edge).min' (finite_constraint_cover_sizes_nonempty edge)

theorem finite_constraint_cover_minimum_le {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) (C : Finset ν) (hC : finiteConstraintCover edge C) :
    finiteConstraintCoverMinimum edge ≤ C.card := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ C), hC⟩, rfl⟩

theorem finite_constraint_cover_minimum_attained {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) :
    ∃ C : Finset ν, finiteConstraintCover edge C ∧ C.card = finiteConstraintCoverMinimum edge := by
  have h := Finset.min'_mem (finiteConstraintCoverSizes edge)
    (finite_constraint_cover_sizes_nonempty edge)
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp h
  exact ⟨C, (Finset.mem_filter.mp hC).2, he⟩

/-- This is a semantic characterization of the computed minimum, proved from
its enumeration. It is not a hypothesis replacing minimum-cover computation. -/
theorem finite_constraint_cover_minimum_spec {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) :
    ∃ C : Finset ν, finiteConstraintCover edge C ∧
      C.card = finiteConstraintCoverMinimum edge ∧
      ∀ D : Finset ν, finiteConstraintCover edge D → C.card ≤ D.card := by
  obtain ⟨C, hC, he⟩ := finite_constraint_cover_minimum_attained edge
  refine ⟨C, hC, he, ?_⟩
  intro D hD
  calc
    C.card = finiteConstraintCoverMinimum edge := he
    _ ≤ D.card := finite_constraint_cover_minimum_le edge D hD

/-- Exact transport to the project's original interval-edge/cover predicates. -/
theorem finite_constraint_cover_interval_bridge {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) (lo hi : ν → ν → ℝ) (M : ℝ)
    (hedge : ∀ a b, edge a b = true ↔ intervalConstraintEdge lo hi M a b)
    (C : Finset ν) :
    finiteConstraintCover edge C ↔ intervalVertexCover (C : Set ν) lo hi M := by
  constructor
  · intro h a b hab
    exact h a b ((hedge a b).mpr hab)
  · intro h a b hab
    exact h a b ((hedge a b).mp hab)

theorem finite_constraint_cover_minimum_set_le {ν : Type*} [Fintype ν] [DecidableEq ν]
    (edge : ν → ν → Bool) (lo hi : ν → ν → ℝ) (M : ℝ)
    (hedge : ∀ a b, edge a b = true ↔ intervalConstraintEdge lo hi M a b)
    (C : Set ν) [DecidablePred (· ∈ C)] (hC : intervalVertexCover C lo hi M) :
    finiteConstraintCoverMinimum edge ≤ Fintype.card C := by
  have hc : finiteConstraintCover edge C.toFinset := by
    intro a b hab
    simpa only [Set.mem_toFinset] using hC a b ((hedge a b).mp hab)
  simpa only [Set.toFinset_card] using finite_constraint_cover_minimum_le edge C.toFinset hc

theorem finite_constraint_cover_minimum_empty_labels {ν : Type*} [Fintype ν]
    [DecidableEq ν] [IsEmpty ν] (edge : ν → ν → Bool) :
    finiteConstraintCoverMinimum edge = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hc : finiteConstraintCover edge ∅ := by
    intro a
    exact isEmptyElim a
  simpa only [Finset.card_empty] using finite_constraint_cover_minimum_le edge ∅ hc

end SparseCompletion
