module

import SDChallenge

open Set Filter Topology TopologicalSpace

universe u

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
    {K : Set X} (hK : IsClosed K) (hG : IsGδ K) :
    ∃ V : ℕ → Set X,
      (∀ n, IsClosed (V n) ∧ V n ∈ 𝓝ˢ K) ∧
      K = ⋂ n, V n ∧
      (𝓝ˢ K).HasBasis (fun _ : Finset ℕ => True) (fun F => ⋂ n ∈ F, V n) :=
  Sneider.exists_closed_countable_nhds_basis_of_isGδ hK hG

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
    {K : Set X} (hK : IsClosed K) (hG : IsGδ K) :
    (𝓝ˢ K).IsCountablyGenerated := Sneider.nhdsSet_isCountablyGenerated_of_isGδ hK hG

example {X : Type u} [TopologicalSpace X] [MetrizableSpace X] :
    IsGδ (diagonal X) := Sneider.isGdelta_diagonal

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) :
    ∃ V : ℕ → Set (X × X),
      (∀ n, IsClosed (V n) ∧ V n ∈ 𝓝ˢ (diagonal X)) ∧
      diagonal X = ⋂ n, V n ∧
      (𝓝ˢ (diagonal X)).HasBasis (fun _ : Finset ℕ => True)
        (fun F => ⋂ n ∈ F, V n) := Sneider.exists_closed_diagonal_basis hD

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) : MetrizableSpace X :=
  Sneider.metrizableSpace_of_isGdelta_diagonal hD

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ IsGδ (diagonal X) := Sneider.metrizable_iff_isGdelta_diagonal

example {X : Type u} [t : TopologicalSpace X] [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t :=
  Sneider.exists_compatibleMetric hD

-- Explicitly pin the diagonal to the standard product topology of the given t.
example {X : Type u} [t : TopologicalSpace X] [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ @IsGδ (X × X) (instTopologicalSpaceProd) (diagonal X) :=
  Sneider.metrizable_iff_isGdelta_diagonal
