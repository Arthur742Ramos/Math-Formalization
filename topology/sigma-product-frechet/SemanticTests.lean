module

import SigmaSolution
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Cardinality

open Set Filter Topology SigmaFrechet

-- The index may be empty; the proof must not require a coordinate to enumerate.
example : FrechetUrysohnSpace (SigmaProduct (X := fun _ : Empty => Bool) (fun _ => false)) :=
  frechetUrysohnSpace _

-- An arbitrary real-indexed product is used, not a countable-index proxy.
example : FrechetUrysohnSpace (SigmaProduct (X := fun _ : ℝ => Bool) (fun _ => false)) :=
  frechetUrysohnSpace _

-- Factor and index universes need not coincide.
example : FrechetUrysohnSpace
    (SigmaProduct (X := fun _ : ULift.{1} ℝ => Bool) (fun _ => false)) :=
  frechetUrysohnSpace _

-- First countability is enough, even for an indiscrete, non-T1 factor topology.
example :
    letI : TopologicalSpace Bool := ⊤
    FrechetUrysohnSpace (SigmaProduct (X := fun _ : ℝ => Bool) (fun _ => false)) := by
  let _ : TopologicalSpace Bool := ⊤
  exact frechetUrysohnSpace _

example : letI : TopologicalSpace Bool := ⊤; ¬ T1Space Bool := by
  let _ : TopologicalSpace Bool := ⊤
  intro h
  let := h
  have ho : IsOpen ({false}ᶜ : Set Bool) := isClosed_singleton.isOpen_compl
  rcases (TopologicalSpace.isOpen_top_iff _).mp ho with he | hu
  · have ht : true ∈ ({false}ᶜ : Set Bool) := by simp
    rw [he] at ht
    exact ht
  · have hf : false ∈ ({false}ᶜ : Set Bool) := by rw [hu]; trivial
    simp at hf

-- The Solution import must expose both general selected literal values too.
example {ι : Type*} {X : ι → Type*} (b x : ∀ i, X i) :
    deviationSupport b x = {i | x i ≠ b i} := rfl

example {ι : Type*} {X : ι → Type*} (b : ∀ i, X i) :
    SigmaProduct b = {x : ∀ i, X i // {i | x i ≠ b i}.Countable} := rfl

-- The product uses a genuinely arbitrary basepoint, not an implicit zero.
example : Dense {x : ℝ → ℝ | (deviationSupport (fun _ => 42) x).Countable} :=
  dense_countableSupport _

example {ι : Type*} {X : ι → Type*} (b : ∀ i, X i) : deviationSupport b b = ∅ := by
  ext i
  simp [deviationSupport]

-- A large ordinary Boolean cube is not sequential, despite the positive Σ-result.
example : ¬ SequentialSpace (ℝ → Bool) :=
  boolean_cube_not_sequential (not_countable_iff.mpr inferInstance)

-- Closure control requires T1; no such premise occurs in the positive main theorem.
example (s : Set (ℝ → ℝ)) (hs : s.Countable)
    (hp : ∀ y ∈ s, (deviationSupport (fun _ => 42) y).Countable) :
    ∃ J : Set ℝ, J.Countable ∧
      ∀ x ∈ closure s, deviationSupport (fun _ => 42) x ⊆ J :=
  countable_closure_support _ hs hp
