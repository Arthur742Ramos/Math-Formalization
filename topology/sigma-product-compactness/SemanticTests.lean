module

import SigmaCompactSolution
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Cardinality

open Set Filter Topology SigmaCompact

-- Empty index: no coordinate or nonempty support can be chosen.
example : OmegaBounded (SigmaProduct (X := fun _ : Empty => Bool) (fun _ => false)) :=
  omegaBounded_sigmaProduct_of_compact _

example : CompactSpace (SigmaProduct (X := fun _ : Empty => Bool) (fun _ => false)) :=
  (compactSpace_sigmaProduct_iff _).mpr (Set.to_countable _)

-- Genuine uncountable index and arbitrary index universe.
example : CountablyCompactSpace (SigmaProduct (X := fun _ : ℝ => Bool) (fun _ => false)) ∧
    ¬ CompactSpace (SigmaProduct (X := fun _ : ℝ => Bool) (fun _ => false)) :=
  boolean_sigma_countablyCompact_not_compact (not_countable_iff.mpr inferInstance)

example : OmegaBounded
    (SigmaProduct (X := fun _ : ULift.{1} ℝ => Bool) (fun _ => true)) :=
  SigmaCompact.omegaBounded_sigmaProduct_of_compact _

-- Countable support includes infinitely many changes, rather than finite support.
example : CompactSpace (SigmaProduct (X := fun _ : ℕ => Bool) (fun _ => true)) :=
  (compactSpace_sigmaProduct_iff _).mpr (Set.to_countable _)

example : (deviationSupport (fun _ : ℕ => false) (fun _ => true)).Infinite := by
  simpa [deviationSupport] using Set.infinite_univ (α := ℕ)

-- An uncountable index of singleton factors is compact. Index countability is
-- not the criterion: only coordinates that can actually change are counted.
example : CompactSpace (SigmaProduct (X := fun _ : ℝ => Unit) (fun _ => ())) :=
  (compactSpace_sigmaProduct_iff _).mpr (by simp [activeCoordinates])

-- A nonzero basepoint in compact real-interval factors.
example : OmegaBounded
    (SigmaProduct (X := fun _ : ℝ => Set.Icc (0 : ℝ) 1) (fun _ => ⟨1, by norm_num⟩)) :=
  omegaBounded_sigmaProduct_of_compact _

-- The compact-trap construction must handle the empty countable subset.
example : ∃ (J : Set Empty) (K : Set (Empty → Bool)), J.Countable ∧ IsClosed K ∧
    IsCompact K ∧ closure (∅ : Set (Empty → Bool)) ⊆ K ∧
    ∀ x ∈ K, deviationSupport (fun _ => false) x ⊆ J :=
  SigmaCompact.exists_compact_trap _ (fun _ _ _ => isClosed_closure.isCompact)
    countable_empty (by simp)

-- Solution exposes the selected literal definitions separately from Challenge.
example {Y : Type*} [TopologicalSpace Y] :
    SigmaCompact.OmegaBounded Y ↔ ∀ s : Set Y, s.Countable → IsCompact (closure s) := Iff.rfl

example {ι : Type*} {X : ι → Type*} (b x : ∀ i, X i) :
    SigmaCompact.deviationSupport b x = {i | x i ≠ b i} := rfl

example {ι : Type*} {X : ι → Type*} (b : ∀ i, X i) :
    SigmaCompact.activeCoordinates b = {i | ∃ x : X i, x ≠ b i} := rfl
