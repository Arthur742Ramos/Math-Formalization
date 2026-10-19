module
public import ProductCCCChallenge
open ProductCCC Set TopologicalSpace
#check ProductCCC.HasCCC
#check ProductCCC.IsDeltaSystem
#check ProductCCC.uncountable_delta_system
#check ProductCCC.hasCCC_pi_of_finite
#check ProductCCC.hasCCC_pi_iff
#check ProductCCC.hasCCC_pi_of_separable
#check ProductCCC.HasCCC.of_continuous_surjective
#check ProductCCC.hasCCC_discrete_iff

-- Independent universes and arbitrary factor spaces: no hidden metrizability/separation.
example {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (h : ∀ s : Finset ι, HasCCC (∀ i : s, X i)) : HasCCC (∀ i, X i) :=
  hasCCC_pi_of_finite h

example {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, Nonempty (X i)] : HasCCC (∀ i, X i) ↔
      ∀ s : Finset ι, HasCCC (∀ i : s, X i) := hasCCC_pi_iff

example {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, SeparableSpace (X i)] : HasCCC (∀ i, X i) := hasCCC_pi_of_separable

example {α : Type u} {I : Type v} (s : I → Finset α) (J : Set I)
    (h : ¬J.Countable) : ∃ K ⊆ J, ¬K.Countable ∧ ∃ r, IsDeltaSystem s K r :=
  uncountable_delta_system s J h

-- Selected definitions have literal audited values in this independent entrypoint.
example (X : Type*) [TopologicalSpace X] : HasCCC X ↔
    ∀ A : Set (Set X), (∀ U ∈ A, IsOpen U ∧ U.Nonempty) →
      A.Pairwise Disjoint → A.Countable := Iff.rfl

example {I α : Type*} (s : I → Finset α) (J : Set I) (r : Finset α) : (by
    classical
    exact (IsDeltaSystem s J r ↔ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → s i ∩ s j = r)) := by
  classical
  exact Iff.rfl

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : HasCCC X) (f : X → Y) (hf : Continuous f) (hs : Function.Surjective f) :
    HasCCC Y := h.of_continuous_surjective hf hs

example (X : Type u) [TopologicalSpace X] [DiscreteTopology X] :
    HasCCC X ↔ Countable X := hasCCC_discrete_iff X
