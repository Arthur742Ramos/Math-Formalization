module

import CCChallenge
open Set Function Topology TopologicalSpace CountableCoordinates
universe u v w
variable {I : Type u} {A : I → Type v} {B : Type w}
  [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
  [∀ i, T2Space (A i)] [∀ i, Nonempty (A i)]
  [TopologicalSpace B] [MetrizableSpace B]

example {f : (∀ i, A i) → B} (hf : Continuous f) :
    ∃ s : Set I, s.Countable ∧ ∃ g : (∀ i : s, A i) → B,
      Continuous g ∧ f = g ∘ s.domRestrict :=
  exists_countable_continuous_factorization hf

example : MetrizableSpace (∀ i, A i) ↔
    (∀ i, MetrizableSpace (A i)) ∧ {i | Nontrivial (A i)}.Countable :=
  compact_product_metrizable_iff

example (a : ∀ i, A i) (s : Set I) (z : ∀ i : s, A i) (i : I) (hi : i ∈ s) :
    refill a s z i = z ⟨i, hi⟩ := by
  simp [refill, hi]

example (a : ∀ i, A i) (s : Set I) (z : ∀ i : s, A i) (i : I) (hi : i ∉ s) :
    refill a s z i = a i := by
  simp [refill, hi]

#check CountableCoordinates.finite_coordinates_of_entourage
#check CountableCoordinates.countable_coordinates_of_uniformContinuous
#check CountableCoordinates.countable_coordinates_of_continuous
#check CountableCoordinates.restrict_refill
#check CountableCoordinates.uniformContinuous_refill
#check CountableCoordinates.exists_countable_uniform_factorization
#check CountableCoordinates.exists_countable_continuous_factorization
#check CountableCoordinates.factor_unique
#check CountableCoordinates.exists_common_countable_factorization
#check CountableCoordinates.nontrivial_subset_of_injective
#check CountableCoordinates.countable_nontrivial_of_continuous_injective
#check CountableCoordinates.continuous_refill
#check CountableCoordinates.compact_product_metrizable_iff
#check CountableCoordinates.refill
