/-
Released under the repository Apache 2.0 license.
Substantive formalization: OpenAI Codex, under Arthur's authorization.
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Compact Hausdorff countable-network metrization

Network members are arbitrary subsets, not necessarily open or neighborhoods.
The main bridge constructs bounded continuous separating functions from pairs
of network sets with disjoint closures. Compactness then gives metrizability.

The classical criterion is used in F. D. Tall, Countable Tightness and the
Grothendieck Property in Cp-Theory, arXiv:2007.08579v1, printed p.8, and in
G. Gruenhage, Spaces having a small diagonal, arXiv:math/9910153v1, printed p.5.
-/

@[expose] public section

open Set Topology TopologicalSpace

namespace CountableNetwork

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A network refines every open neighborhood at its point. Its members need
not themselves be open, closed, or neighborhoods. -/
def IsNetwork (N : Set (Set X)) : Prop :=
  ∀ U, IsOpen U → ∀ x ∈ U, ∃ A ∈ N, x ∈ A ∧ A ⊆ U

/-- Existence of a countable network of arbitrary subsets. -/
def HasCountableNetwork (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ N : Set (Set X), N.Countable ∧ IsNetwork N

/-- Normal shrinking and Urysohn separation turn network pairs into bounded
continuous functions separating all distinct points. No compactness or
countability is needed for this indexed-family construction. -/
theorem IsNetwork.exists_bounded_separating_family [NormalSpace X] [T3Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ f : (N × N) → C(X, ℝ),
      (∀ i x, f i x ∈ Icc (0 : ℝ) 1) ∧
      Pairwise (fun x y => ∃ i, f i x ≠ f i y) := by
  classical
  have hex (i : N × N) : ∃ f : C(X, ℝ),
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      (Disjoint (closure (i.1 : Set X)) (closure (i.2 : Set X)) →
        EqOn f 0 (closure (i.1 : Set X)) ∧ EqOn f 1 (closure (i.2 : Set X))) := by
    by_cases hd : Disjoint (closure (i.1 : Set X)) (closure (i.2 : Set X))
    · obtain ⟨f, hf0, hf1, hfb⟩ :=
        exists_continuous_zero_one_of_isClosed isClosed_closure isClosed_closure hd
      exact ⟨f, hfb, fun _ => ⟨hf0, hf1⟩⟩
    · exact ⟨0, fun _ => by simp, fun h => (hd h).elim⟩
  choose f hfb hfs using hex
  refine ⟨f, hfb, ?_⟩
  intro x y hxy
  obtain ⟨U, hxU, hU, V, hyV, hV, hd⟩ := exists_open_nhds_disjoint_closure hxy
  obtain ⟨A, hAN, hxA, hAU⟩ := hN U hU x hxU
  obtain ⟨B, hBN, hyB, hBV⟩ := hN V hV y hyV
  let i : N × N := (⟨A, hAN⟩, ⟨B, hBN⟩)
  have hab : Disjoint (closure A) (closure B) :=
    hd.mono (closure_mono hAU) (closure_mono hBV)
  have hx : f i x = 0 := (hfs i hab).1 (subset_closure hxA)
  have hy : f i y = 1 := (hfs i hab).2 (subset_closure hyB)
  exact ⟨i, by rw [hx, hy]; norm_num⟩

/-- A compact Hausdorff space with a countable network is metrizable. The
countable network is not assumed to be a base or to consist of open sets. -/
theorem metrizableSpace_of_countable_network [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hc : N.Countable) (hN : IsNetwork N) : MetrizableSpace X := by
  classical
  let : Encodable N := hc.toEncodable
  obtain ⟨f, _, hf⟩ := hN.exists_bounded_separating_family
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating (fun i x => f i x)
    (fun i => (f i).continuous) hf

/-- A second-countable space has a countable network, without separation or
compactness assumptions. -/
theorem hasCountableNetwork_of_secondCountable [SecondCountableTopology X] :
    HasCountableNetwork X := by
  obtain ⟨B, hc, _, hB⟩ := exists_countable_basis X
  refine ⟨B, hc, ?_⟩
  intro U hU x hx
  exact hB.mem_nhds_iff.mp (hU.mem_nhds hx)

/-- Full compact Hausdorff equivalence, allowing empty spaces. -/
theorem metrizable_iff_hasCountableNetwork [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ HasCountableNetwork X := by
  constructor
  · intro h
    let := h
    let := metrizableSpaceMetric X
    exact hasCountableNetwork_of_secondCountable
  · rintro ⟨N, hc, hN⟩
    exact metrizableSpace_of_countable_network hc hN

/-- In compact Hausdorff spaces, a countable network is equivalent to an
actual countable open base. -/
theorem secondCountable_iff_hasCountableNetwork [CompactSpace X] [T2Space X] :
    SecondCountableTopology X ↔ HasCountableNetwork X := by
  constructor
  · intro h
    let := h
    exact hasCountableNetwork_of_secondCountable
  · intro h
    let := metrizable_iff_hasCountableNetwork.mpr h
    let := metrizableSpaceMetric X
    infer_instance

/-- The criterion returns a metric inducing exactly the supplied topology. -/
theorem exists_compatibleMetric [CompactSpace X] [T2Space X]
    (h : HasCountableNetwork X) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X› := by
  have : MetrizableSpace X := metrizable_iff_hasCountableNetwork.mpr h
  exact ⟨metrizableSpaceMetric X, rfl⟩

/-- A network yields a closed embedding of a compact Hausdorff space into a
product of real intervals, expressed as bounded real coordinates. -/
theorem IsNetwork.exists_closedEmbedding [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ F : X → ((N × N) → ℝ), IsClosedEmbedding F ∧
      ∀ x i, F x i ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hfb, hfs⟩ := hN.exists_bounded_separating_family
  let F : X → ((N × N) → ℝ) := fun x i => f i x
  have hF : Continuous F := continuous_pi fun i => (f i).continuous
  have hFi : Function.Injective F := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hi⟩ := hfs hne
    exact hi (congrFun hxy i)
  exact ⟨F, hF.isClosedEmbedding hFi, fun x i => hfb i x⟩

/-- Arbitrary networks push forward under continuous surjections. -/
theorem IsNetwork.image {N : Set (Set X)} (hN : IsNetwork N) {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : IsNetwork ((Set.image f) '' N) := by
  intro U hU y hy
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨A, hAN, hxA, hAU⟩ := hN (f ⁻¹' U) (hU.preimage hf) x hy
  refine ⟨f '' A, ⟨A, hAN, rfl⟩, ⟨x, hxA, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hAU hz

/-- A continuous surjective image of a countable-network space again has a
countable network. No separation or compactness is assumed here. -/
theorem HasCountableNetwork.of_continuous_surjective (h : HasCountableNetwork X)
    {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    HasCountableNetwork Y := by
  obtain ⟨N, hc, hN⟩ := h
  exact ⟨(Set.image f) '' N, hc.image _, hN.image hf hs⟩

/-- Having a countable network is hereditary to every subspace, including
nonclosed and empty subspaces. -/
theorem HasCountableNetwork.subtype (h : HasCountableNetwork X) (S : Set X) :
    HasCountableNetwork S := by
  obtain ⟨N, hc, hN⟩ := h
  refine ⟨(fun A : Set X => (Subtype.val : S → X) ⁻¹' A) '' N, hc.image _, ?_⟩
  intro U hU x hx
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨A, hAN, hxA, hAV⟩ := hN V hV x.val hx
  exact ⟨Subtype.val ⁻¹' A, ⟨A, hAN, rfl⟩, hxA, fun _ hz => hAV hz⟩

/-- Every compact subspace of a Hausdorff countable-network space is
metrizable, even when the ambient space is not compact or metrizable. -/
theorem metrizable_compact_subspace [T2Space X] (h : HasCountableNetwork X)
    {S : Set X} (hS : IsCompact S) : MetrizableSpace S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  exact metrizable_iff_hasCountableNetwork.mpr (h.subtype S)

end CountableNetwork
