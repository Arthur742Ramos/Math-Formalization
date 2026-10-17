/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
and Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Material Lean proof authorship: OpenAI Codex, under the authorized campaign.
-/
module

public import Mathlib.Topology.UniformSpace.OfCompactT2
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Metrizable.Uniformity

@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace UniformSpace
open scoped Topology Uniformity
namespace CountableCoordinates

variable {ι : Type*} {X : ι → Type*} {Y : Type*}

/-- Every entourage in a product contains all pairs agreeing on some finite set
of coordinates. This asserts exact agreement, not a uniform bound on coordinates. -/
theorem finite_coordinates_of_entourage [∀ i, UniformSpace (X i)]
    {V : Set ((∀ i, X i) × (∀ i, X i))} (hV : V ∈ 𝓤 (∀ i, X i)) :
    ∃ s : Set ι, s.Finite ∧ ∀ x y, (∀ i ∈ s, x i = y i) → (x, y) ∈ V := by
  rw [Pi.uniformity] at hV
  rcases Filter.mem_iInf.mp hV with ⟨s, hs, W, hW, rfl⟩
  refine ⟨s, hs, fun x y hxy => mem_iInter.mpr fun i => ?_⟩
  rcases Filter.mem_comap.mp (hW i) with ⟨t, ht, hta⟩
  apply hta
  change (x i, y i) ∈ t
  rw [hxy i i.2]
  exact refl_mem_uniformity ht

/-- A uniformly continuous map to a separated, countably generated uniform
space is determined by countably many input coordinates. -/
theorem countable_coordinates_of_uniformContinuous [∀ i, UniformSpace (X i)]
    [UniformSpace Y] [T0Space Y] [(𝓤 Y).IsCountablyGenerated]
    {f : (∀ i, X i) → Y} (hf : UniformContinuous f) :
    ∃ s : Set ι, s.Countable ∧ ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y := by
  obtain ⟨V, hV⟩ := (𝓤 Y).exists_antitone_basis
  have hfin (n : ℕ) : ∃ s : Set ι, s.Finite ∧
      ∀ x y, (∀ i ∈ s, x i = y i) → (f x, f y) ∈ V n :=
    finite_coordinates_of_entourage (hf (hV.1.mem_of_mem (by trivial)))
  choose s hs hsf using hfin
  refine ⟨⋃ n, s n, countable_iUnion (fun n => (hs n).countable), ?_⟩
  intro x y hxy
  apply eq_of_uniformity_basis hV.1
  intro n _
  exact hsf n x y (fun i hi => hxy i (mem_iUnion.mpr ⟨n, hi⟩))

/-- A continuous map from an arbitrary product of compact Hausdorff spaces to
any metrizable space depends on a countable set of coordinates. -/
theorem countable_coordinates_of_continuous [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : (∀ i, X i) → Y} (hf : Continuous f) :
    ∃ s : Set ι, s.Countable ∧ ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y := by
  let : ∀ i, UniformSpace (X i) := fun _ => uniformSpaceOfCompactR1
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (𝓤 Y).IsCountablyGenerated := pseudoMetrizableSpaceUniformity_countably_generated Y
  exact countable_coordinates_of_uniformContinuous
    (CompactSpace.uniformContinuous_of_continuous hf)

/-- Refill omitted coordinates from a fixed basepoint; retain every selected
coordinate exactly. The basepoint makes this a section on the whole subproduct. -/
def refill (a : ∀ i, X i) (s : Set ι) (z : ∀ i : s, X i) (i : ι) : X i := by
  classical
  exact if hi : i ∈ s then z ⟨i, hi⟩ else a i

/-- Restricting a refilled point recovers the original subproduct point. -/
theorem restrict_refill (a : ∀ i, X i) (s : Set ι) (z : ∀ i : s, X i) :
    s.domRestrict (refill a s z) = z := by
  funext i
  simp [refill, i.2]

/-- The refill section is uniformly continuous for the product uniformities. -/
theorem uniformContinuous_refill [∀ i, UniformSpace (X i)]
    (a : ∀ i, X i) (s : Set ι) : UniformContinuous (refill a s) := by
  apply uniformContinuous_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simpa only [refill, dite_eq_left hi] using Pi.uniformContinuous_proj (fun j : s => X j) ⟨i, hi⟩
  · simpa only [refill, dite_eq_right hi] using (uniformContinuous_const :
      UniformContinuous (fun _ : (∀ j : s, X j) => a i))

/-- A uniformly continuous map factors through a countable subproduct, with a
uniformly continuous factor. The selected projection has a global section. -/
theorem exists_countable_uniform_factorization [∀ i, UniformSpace (X i)]
    [UniformSpace Y] [T0Space Y] [(𝓤 Y).IsCountablyGenerated]
    (a : ∀ i, X i) {f : (∀ i, X i) → Y} (hf : UniformContinuous f) :
    ∃ s : Set ι, s.Countable ∧ ∃ g : (∀ i : s, X i) → Y,
      UniformContinuous g ∧ f = g ∘ s.domRestrict := by
  obtain ⟨s, hs, hsf⟩ := countable_coordinates_of_uniformContinuous hf
  refine ⟨s, hs, f ∘ refill a s, hf.comp (uniformContinuous_refill a s), ?_⟩
  funext x
  exact hsf x (refill a s (s.domRestrict x)) (fun i hi => by simp [refill, hi])

/-- Continuous compact-product countable-coordinate factorization. Nonempty
factors allow a basepoint, so the factor is defined on the entire subproduct. -/
theorem exists_countable_continuous_factorization [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : (∀ i, X i) → Y} (hf : Continuous f) :
    ∃ s : Set ι, s.Countable ∧ ∃ g : (∀ i : s, X i) → Y,
      Continuous g ∧ f = g ∘ s.domRestrict := by
  let : ∀ i, UniformSpace (X i) := fun _ => uniformSpaceOfCompactR1
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (𝓤 Y).IsCountablyGenerated := pseudoMetrizableSpaceUniformity_countably_generated Y
  obtain ⟨s, hs, g, hg, hfg⟩ := exists_countable_uniform_factorization
    (fun i => Classical.choice (inferInstance : Nonempty (X i)))
    (CompactSpace.uniformContinuous_of_continuous hf)
  exact ⟨s, hs, g, hg.continuous, hfg⟩

/-- For a fixed coordinate set with a basepoint section, the factor map is
unique; continuity is not needed for uniqueness. -/
theorem factor_unique (a : ∀ i, X i) (s : Set ι)
    {g h : (∀ i : s, X i) → Y} (hgh : g ∘ s.domRestrict = h ∘ s.domRestrict) :
    g = h := by
  funext z
  have he := congrFun hgh (refill a s z)
  simpa only [comp_apply, restrict_refill] using he

/-- Canonical countable-product metrizability from Mathlib's product
uniformity and compatible countably generated factor uniformities. -/
theorem metrizable_countable_product [Countable ι]
    [∀ i, TopologicalSpace (X i)] [∀ i, MetrizableSpace (X i)] :
    MetrizableSpace (∀ i, X i) := by
  let : ∀ i, UniformSpace (X i) := fun i => pseudoMetrizableSpaceUniformity (X i)
  have : ∀ i, (𝓤 (X i)).IsCountablyGenerated :=
    fun i => pseudoMetrizableSpaceUniformity_countably_generated (X i)
  infer_instance

/-- A countable family of maps to metrizable spaces shares one countable
coordinate set and factors continuously through that subproduct. -/
theorem exists_common_countable_factorization {J : Type*} [Countable J]
    {Z : J → Type*} [∀ j, TopologicalSpace (Z j)] [∀ j, MetrizableSpace (Z j)]
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]
    (f : ∀ j, (∀ i, X i) → Z j) (hf : ∀ j, Continuous (f j)) :
    ∃ s : Set ι, s.Countable ∧ ∃ g : ∀ j, (∀ i : s, X i) → Z j,
      (∀ j, Continuous (g j)) ∧ ∀ j x, f j x = g j (s.domRestrict x) := by
  have : MetrizableSpace (∀ j, Z j) := metrizable_countable_product
  obtain ⟨s, hs, g, hg, hfg⟩ := exists_countable_continuous_factorization
    (f := fun x j => f j x) (continuous_pi hf)
  exact ⟨s, hs, fun j z => g z j, fun j => (continuous_apply j).comp hg,
    fun j x => congrFun (congrFun hfg x) j⟩

/-- An injective map cannot omit any nontrivial coordinate from a determining
set, provided the product has a basepoint. This lemma is purely set theoretic. -/
theorem nontrivial_subset_of_injective (a : ∀ i, X i) {f : (∀ i, X i) → Y}
    (hf : Injective f) {s : Set ι}
    (hs : ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) :
    {i | Nontrivial (X i)} ⊆ s := by
  classical
  intro i hi
  by_contra his
  obtain ⟨u, v, huv⟩ := hi.exists_pair_ne
  have he := hf (hs (update a i u) (update a i v) (by
    intro j hj
    have hji : j ≠ i := fun e => his (e ▸ hj)
    simp [update_of_ne hji]))
  exact huv (by simpa using congrFun he i)

/-- A continuous injection from a nonempty compact Hausdorff product to a
metrizable target forces at most countably many nontrivial factors. -/
theorem countable_nontrivial_of_continuous_injective
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : (∀ i, X i) → Y} (hf : Continuous f) (hinj : Injective f) :
    {i | Nontrivial (X i)}.Countable := by
  obtain ⟨s, hs, hsf⟩ := countable_coordinates_of_continuous hf
  exact hs.mono (nontrivial_subset_of_injective
    (fun i => Classical.choice (inferInstance : Nonempty (X i))) hinj hsf)

/-- A basepoint refill section is continuous for arbitrary product topologies. -/
theorem continuous_refill [∀ i, TopologicalSpace (X i)]
    (a : ∀ i, X i) (s : Set ι) : Continuous (refill a s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [refill, dite_eq_left hi] using
      (continuous_apply (⟨i, hi⟩ : s) : Continuous (fun z : (∀ j : s, X j) => z ⟨i, hi⟩))
  · simpa only [refill, dite_eq_right hi] using
      (continuous_const : Continuous (fun _ : (∀ j : s, X j) => a i))

/-- Exact metrizability criterion for nonempty compact Hausdorff products.
The index type may be arbitrary; singleton factors need not be countable. -/
theorem compact_product_metrizable_iff [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] :
    MetrizableSpace (∀ i, X i) ↔
      (∀ i, MetrizableSpace (X i)) ∧ {i | Nontrivial (X i)}.Countable := by
  classical
  let a : ∀ i, X i := fun i => Classical.choice (inferInstance : Nonempty (X i))
  constructor
  · intro hm
    have : MetrizableSpace (∀ i, X i) := hm
    refine ⟨fun i => ?_, countable_nontrivial_of_continuous_injective
      (f := id) continuous_id injective_id⟩
    have hleft : LeftInverse (fun x : (∀ i, X i) => x i) (update a i) := by
      intro x
      simp
    exact (hleft.isEmbedding (continuous_apply i)
      (continuous_const.update i continuous_id)).metrizableSpace
  · rintro ⟨hm, hc⟩
    have : ∀ i, MetrizableSpace (X i) := hm
    let s : Set ι := {i | Nontrivial (X i)}
    have : Countable s := hc.to_subtype
    have : MetrizableSpace (∀ i : s, X i) := metrizable_countable_product
    have hleft : LeftInverse (refill a s) s.domRestrict := by
      intro x
      funext i
      by_cases hi : Nontrivial (X i)
      · simp [refill, s, hi]
      · have : Subsingleton (X i) := not_nontrivial_iff_subsingleton.mp hi
        exact Subsingleton.elim _ _
    exact (hleft.isEmbedding (continuous_refill a s)
      (Pi.continuous_domRestrict s)).metrizableSpace

end CountableCoordinates
