/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Reduction
@[expose] public section
open Set Topology TopologicalSpace Filter
universe u v
namespace WhitneyReversibility
variable {X : Type u} [mX : MetricSpace X] [cX : CompactSpace X]

/-- Abo-Zeid's Theorem 2.1 in relative form inside a nondegenerate subcontinuum. -/
theorem exists_indecomposable_covering_family {μ : Continuum X → ℝ}
    (hμ : IsWhitneyMap μ) (Y : Continuum X)
    (_hYnt : (Y.val : Set X).Nontrivial) (hi : ¬ IsDecomposable (Y.val : Set X))
    {t : ℝ} (ht : 0 < t) (htY : t < μ Y) :
    ∃ S : Set (Continuum X), S ⊆ relativeLevel μ Y t ∧ IsCompact S ∧
      IsConnected S ∧ S.Nontrivial ∧ ¬ IsDecomposable S ∧
      familyUnion S = (Y.val : Set X) := by
  classical
  have hs := hμ.isSizeMap
  obtain ⟨S, hSL, hSc, hSn, hSU, hmin⟩ := exists_minimal_covering_family
    (isCompact_relativeLevel hs Y t) (isConnected_relativeLevel hs Y ht.le htY.le) Y
    (fun _ hK => hK.1) (familyUnion_relativeLevel hs Y ht.le htY.le)
  have hSi : ¬ IsDecomposable S := minimal_covering_family_indecomposable
    Y hi hSL (fun _ hK => hK.1) hSU hmin
  have hSnt : S.Nontrivial := by
    by_contra hn
    have hsub : S.Subsingleton := Set.not_nontrivial_iff.mp hn
    obtain ⟨K, hKS⟩ := hSn.nonempty
    have he : S = {K} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨hKS, fun A hAS => hsub hAS hKS⟩
    have hKY : K = Y := by
      apply Subtype.ext
      apply NonemptyCompacts.ext
      simpa only [he, familyUnion, biUnion_singleton] using hSU
    have hKt := (hSL hKS).2
    rw [hKY] at hKt
    exact (ne_of_lt htY) hKt.symm
  exact ⟨S, hSL, hSc, hSn, hSnt, hSi, hSU⟩

/-- The source-faithful positive levels tending to zero detect hereditary decomposability. -/
theorem sequential_strong_whitney_reversibility [cnX : ConnectedSpace X]
    {μ : Continuum X → ℝ} (hμ : IsWhitneyMap μ) (t : ℕ → ℝ)
    (ht : ∀ n, 0 < t n ∧ t n < μ whole)
    (htend : Tendsto t atTop (nhds 0))
    (hlevels : ∀ n, IsHereditarilyDecomposable {K : Continuum X | μ K = t n}) :
    IsHereditarilyDecomposable (univ : Set X) := by
  classical
  intro K _ hKc hKn hKnt
  by_contra hi
  let Y : Continuum X := ⟨⟨⟨K, hKc⟩, hKn.nonempty⟩, hKn⟩
  have hYnt : (Y.val : Set X).Nontrivial := hKnt
  obtain ⟨x, hx, y, hy, hxy⟩ := hKnt
  have hproper : (singleton x).val < Y.val := by
    refine lt_of_le_of_ne (Set.singleton_subset_iff.mpr hx) ?_
    intro he
    have hmem : y ∈ ({x} : Set X) := by
      rw [show ({x} : Set X) = (Y.val : Set X) from congrArg SetLike.coe he]
      exact hy
    exact hxy (Set.mem_singleton_iff.mp hmem).symm
  have hμY : 0 < μ Y := by
    simpa only [hμ.2.1] using hμ.2.2 (singleton x) Y hproper
  have hevent : ∀ᶠ n in atTop, t n < μ Y :=
    htend.eventually (Iio_mem_nhds hμY)
  obtain ⟨n, hn⟩ := hevent.exists
  obtain ⟨S, hSL, hSc, hSn, hSnt, hSi, _⟩ :=
    exists_indecomposable_covering_family hμ Y hYnt hi (ht n).1 hn
  exact hSi (hlevels n S (fun A hA => (hSL hA).2) hSc hSn hSnt)

end WhitneyReversibility

#print axioms WhitneyReversibility.exists_indecomposable_covering_family
#print axioms WhitneyReversibility.sequential_strong_whitney_reversibility
