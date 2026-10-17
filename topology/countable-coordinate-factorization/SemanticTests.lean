module

import CCSolution
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Cardinality

open Set Function Topology TopologicalSpace CountableCoordinates

-- Empty index products remain inhabited singleton spaces.
example (f : (Empty → Unit) → ℝ) (hf : Continuous f) :
    ∃ s : Set Empty, s.Countable ∧ ∃ g : (s → Unit) → ℝ,
      Continuous g ∧ f = g ∘ s.domRestrict :=
  exists_countable_continuous_factorization hf

-- The common factorization allows an empty family of maps.
example (f : Empty → (ℝ → Bool) → Unit) (hf : ∀ j, Continuous (f j)) :
    ∃ s : Set ℝ, s.Countable ∧ ∃ g : Empty → (s → Bool) → Unit,
      (∀ j, Continuous (g j)) ∧ ∀ j x, f j x = g j (s.domRestrict x) :=
  exists_common_countable_factorization f hf

-- An uncountable index is permitted when all its factors are singletons.
example : MetrizableSpace (ℝ → Unit) := by
  apply compact_product_metrizable_iff.mpr
  refine ⟨fun _ => inferInstance, ?_⟩
  have he : {i : ℝ | Nontrivial Unit} = ∅ := by
    ext i
    constructor
    · intro hi
      obtain ⟨x, y, hxy⟩ := hi.exists_pair_ne
      exact hxy (Subsingleton.elim _ _)
    · intro h
      exact h.elim
  rw [he]
  exact countable_empty

-- Arbitrarily many nontrivial compact factors cannot form a metrizable product.
example [MetrizableSpace (ℝ → Bool)] : False := by
  have hc := countable_nontrivial_of_continuous_injective
    (f := (id : (ℝ → Bool) → (ℝ → Bool))) continuous_id injective_id
  have he : {i : ℝ | Nontrivial Bool} = univ := by
    ext
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    infer_instance
  rw [he] at hc
  exact not_countable_univ hc

-- Countably many coordinates cannot generally be strengthened to finitely many:
-- the identity map on Cantor space needs every coordinate.
example : ¬ ∃ s : Set ℕ, s.Finite ∧ ∀ x y : ℕ → Bool,
    (∀ i ∈ s, x i = y i) → x = y := by
  rintro ⟨s, hs, hsf⟩
  have hsub := nontrivial_subset_of_injective (fun _ : ℕ => false) injective_id hsf
  have he : {i : ℕ | Nontrivial Bool} = univ := by
    ext
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    infer_instance
  rw [he] at hsub
  have : (univ : Set ℕ).Finite := hs.subset hsub
  exact infinite_univ this

-- Exact refill endpoints, including empty selected coordinates.
example {I : Type*} {A : I → Type*} (a : ∀ i, A i) (z : ∀ i : (∅ : Set I), A i) :
    refill a ∅ z = a := by
  funext i
  simp [refill]

-- Coordinate dependence requires no basepoint, including an empty full product.
example (f : (Unit → Empty) → ℝ) (hf : Continuous f) :
    ∃ s : Set Unit, s.Countable ∧ ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y :=
  countable_coordinates_of_continuous hf

-- Separation is necessary in the uniform theorem: an indiscrete target has
-- countably generated uniformity, yet its identity need not have countable support.
open scoped Uniformity in
example :
    @UniformContinuous (ℝ → Bool) (ℝ → Bool) (Pi.uniformSpace (fun _ : ℝ => Bool)) ⊤ id ∧
    (𝓤[(⊤ : UniformSpace (ℝ → Bool))]).IsCountablyGenerated ∧
    ¬ ∃ s : Set ℝ, s.Countable ∧ ∀ x y : ℝ → Bool,
      (∀ i ∈ s, x i = y i) → x = y := by
  refine ⟨?_, ?_, ?_⟩
  · unfold UniformContinuous
    rw [top_uniformity]
    exact Filter.tendsto_top
  · rw [top_uniformity]
    infer_instance
  · rintro ⟨s, hs, hsf⟩
    have hsub := nontrivial_subset_of_injective (fun _ : ℝ => false) injective_id hsf
    have he : {i : ℝ | Nontrivial Bool} = univ := by
      ext
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      infer_instance
    rw [he] at hsub
    exact not_countable_univ (hs.mono hsub)

-- Without a full-product basepoint, restriction need not be surjective:
-- distinct factors can have identical composites on the empty full product.
example :
    ((fun _ : ((∅ : Set Unit) → Empty) => true) ∘ ((∅ : Set Unit).domRestrict : (Unit → Empty) → ((∅ : Set Unit) → Empty))) =
      ((fun _ : ((∅ : Set Unit) → Empty) => false) ∘ ((∅ : Set Unit).domRestrict : (Unit → Empty) → ((∅ : Set Unit) → Empty))) ∧
    (fun _ : ((∅ : Set Unit) → Empty) => true) ≠
      (fun _ : ((∅ : Set Unit) → Empty) => false) := by
  constructor
  · funext x
    exact (x ()).elim
  · intro h
    have he := congrFun h (fun i => i.2.elim)
    cases he
