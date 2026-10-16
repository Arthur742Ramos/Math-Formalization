/-
Released under the repository Apache 2.0 license.
Substantive formalization: OpenAI Codex, under Arthur's authorization.
-/
module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.UniformSpace.OfCompactT2
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Sneider's compact Gδ-diagonal metrization criterion

For a compact Hausdorff space, metrizability is equivalent to the diagonal
being Gδ in the product topology. The substantive bridge proves that a
closed Gδ set in a compact normal space has countable neighborhood character.

Source statement and research setting: G. Gruenhage, Spaces having a small
diagonal, arXiv:math/9910153v1, introduction, printed p.1. This development
proves that classical Gδ-diagonal criterion and does not assert any conclusion
for the weaker small-diagonal property studied in that paper.
-/

@[expose] public section

open Set Filter Topology

namespace Sneider

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]

/-- A closed Gδ set in a compact normal space has a countable neighborhood basis
consisting of finite intersections of closed neighborhoods. -/
theorem exists_closed_countable_nhds_basis_of_isGδ {K : Set X}
    (hK : IsClosed K) (hG : IsGδ K) :
    ∃ V : ℕ → Set X,
      (∀ n, IsClosed (V n) ∧ V n ∈ 𝓝ˢ K) ∧
      K = ⋂ n, V n ∧
      (𝓝ˢ K).HasBasis (fun _ : Finset ℕ => True) (fun F => ⋂ n ∈ F, V n) := by
  classical
  obtain ⟨U, hU, hKU⟩ := hG.eq_iInter_nat
  have hsub (n : ℕ) : K ⊆ U n := by
    rw [hKU]
    exact iInter_subset U n
  choose W hW hKW hWU using fun n => normal_exists_closure_subset hK (hU n) (hsub n)
  let V : ℕ → Set X := fun n => closure (W n)
  have hVmem (n : ℕ) : V n ∈ 𝓝ˢ K :=
    mem_nhdsSet_iff_exists.mpr ⟨W n, hW n, hKW n, subset_closure⟩
  have hKV : K = ⋂ n, V n := by
    apply Subset.antisymm
    · exact subset_iInter fun n => (hKW n).trans subset_closure
    · rw [hKU]
      exact iInter_mono fun n => hWU n
  refine ⟨V, fun n => ⟨isClosed_closure, hVmem n⟩, hKV, ⟨?_⟩⟩
  intro S
  constructor
  · intro hS
    obtain ⟨O, hO, hKO, hOS⟩ := mem_nhdsSet_iff_exists.mp hS
    have hdis : Disjoint Oᶜ (⋂ n, V n) := by
      rw [← hKV]
      exact Set.disjoint_left.mpr fun x hx hxK => hx (hKO hxK)
    obtain ⟨F, hF⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
      V (fun _ => isClosed_closure) hdis
    refine ⟨F, trivial, ?_⟩
    intro x hx
    apply hOS
    by_contra hxO
    exact Set.disjoint_left.mp hF hxO hx
  · rintro ⟨F, _, hFS⟩
    exact mem_of_superset ((biInter_mem F.finite_toSet).mpr fun n _ => hVmem n) hFS

/-- The neighborhood filter of a closed Gδ set in a compact normal space is
countably generated. -/
theorem nhdsSet_isCountablyGenerated_of_isGδ {K : Set X}
    (hK : IsClosed K) (hG : IsGδ K) : (𝓝ˢ K).IsCountablyGenerated := by
  obtain ⟨V, _, _, hV⟩ := exists_closed_countable_nhds_basis_of_isGδ hK hG
  exact hV.isCountablyGenerated


end Sneider

namespace Sneider

open TopologicalSpace
open scoped Uniformity

variable {X : Type*} [TopologicalSpace X]

/-- Every metrizable space has a Gδ diagonal in its square, without a
compactness hypothesis. -/
theorem isGdelta_diagonal [MetrizableSpace X] : IsGδ (diagonal X) :=
  isClosed_diagonal.isGδ

/-- The Gδ diagonal of a compact Hausdorff space admits a cofinal family of
finite intersections of closed diagonal neighborhoods. -/
theorem exists_closed_diagonal_basis [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) :
    ∃ V : ℕ → Set (X × X),
      (∀ n, IsClosed (V n) ∧ V n ∈ 𝓝ˢ (diagonal X)) ∧
      diagonal X = ⋂ n, V n ∧
      (𝓝ˢ (diagonal X)).HasBasis (fun _ : Finset ℕ => True)
        (fun F => ⋂ n ∈ F, V n) :=
  exists_closed_countable_nhds_basis_of_isGδ isClosed_diagonal hD

/-- Sneider sufficiency: the compact Hausdorff topology is induced by a metric
when its diagonal is Gδ. No countability of the underlying space is assumed. -/
theorem metrizableSpace_of_isGdelta_diagonal [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) : MetrizableSpace X := by
  have h : (𝓝ˢ (diagonal X)).IsCountablyGenerated :=
    nhdsSet_isCountablyGenerated_of_isGδ isClosed_diagonal hD
  let : UniformSpace X := uniformSpaceOfCompactR1
  have : (𝓤 X).IsCountablyGenerated := h
  exact UniformSpace.metrizableSpace

/-- Sneider's full equivalence for compact Hausdorff spaces, including the
empty space. The diagonal and Gδ are the standard Mathlib notions. -/
theorem metrizable_iff_isGdelta_diagonal [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ IsGδ (diagonal X) :=
  ⟨fun _ => isGdelta_diagonal, metrizableSpace_of_isGdelta_diagonal⟩

/-- The criterion supplies an actual metric inducing exactly the given
compact Hausdorff topology. -/
theorem exists_compatibleMetric [CompactSpace X] [T2Space X]
    (hD : IsGδ (diagonal X)) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X› := by
  have : MetrizableSpace X := metrizableSpace_of_isGdelta_diagonal hD
  exact ⟨metrizableSpaceMetric X, rfl⟩

end Sneider
