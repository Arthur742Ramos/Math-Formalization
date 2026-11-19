module

public import BoundedEdgeRegularSubgraphs.BlockRegularAmplification
public import BoundedEdgeRegularSubgraphs.InducedDegreeTargets
public import BoundedEdgeRegularSubgraphs.RowSampleApproximation
public import BoundedEdgeRegularSubgraphs.CellRowBalance
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Order.Hom.Set
import Mathlib.Tactic

/-!
# Transporting order events and normalized expected degrees
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]

private noncomputable def mappedSubsetIso (f : α ≃o β) (S : Finset α) :
    S ≃o ↥(S.map f.toEquiv.toEmbedding) where
  toFun i := ⟨f i, Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩
  invFun j := ⟨f.symm j, by
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp j.property
    change f i = j.val at he
    rw [← he, f.symm_apply_apply]
    exact hi⟩
  left_inv i := Subtype.ext (f.symm_apply_apply i)
  right_inv j := Subtype.ext (f.apply_symm_apply j)
  map_rel_iff' := f.le_iff_le

private theorem exactOrderEvent_of_reindexed (f : α ≃o β) (w : Edge β → ℝ) (k : ℕ)
    (h : w ∘ edgeEquiv f ∈ exactOrderEvent k) : w ∈ exactOrderEvent k := by
  classical
  obtain ⟨S, hS⟩ := Set.mem_iUnion.mp h
  let T := S.val.map f.toEquiv.toEmbedding
  let g : S.val ≃o T := mappedSubsetIso f S.val
  have hT : T.card = k := (Finset.card_map _).trans S.property
  apply Set.mem_iUnion.mpr
  refine ⟨⟨T, hT⟩, ?_⟩
  change ∀ i j : T, degreeSum (induce T w) i = degreeSum (induce T w) j
  change ∀ i j : S.val, degreeSum (induce S.val (w ∘ edgeEquiv f)) i =
    degreeSum (induce S.val (w ∘ edgeEquiv f)) j at hS
  have he : induce S.val (w ∘ edgeEquiv f) = induce T w ∘ edgeEquiv g := by
    funext e
    rfl
  rw [he] at hS
  simp_rw [degreeSum_reindex g] at hS
  intro i j
  simpa only [g.apply_symm_apply] using hS (g.symm i) (g.symm j)

theorem exactOrderEvent_reindex_iff (f : α ≃o β) (w : Edge β → ℝ) (k : ℕ) :
    w ∘ edgeEquiv f ∈ exactOrderEvent k ↔ w ∈ exactOrderEvent k := by
  refine ⟨exactOrderEvent_of_reindexed f w k, ?_⟩
  intro h
  apply exactOrderEvent_of_reindexed f.symm (w ∘ edgeEquiv f) k
  have he : (w ∘ edgeEquiv f) ∘ edgeEquiv f.symm = w := by
    funext e
    apply congrArg w
    apply Subtype.ext
    exact Prod.ext (f.apply_symm_apply _) (f.apply_symm_apply _)
  rwa [he]

theorem probability_exactOrder_failure_reindex (f : α ≃o β) (p : Edge β → Icc (0 : ℝ) 1) (k : ℕ) :
    (graphLaw (p ∘ edgeEquiv f)).real (exactOrderEvent k)ᶜ =
      (graphLaw p).real (exactOrderEvent k)ᶜ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Edge β ↦ ℝ) (edgeEquiv f)
  have hmap : MeasurePreserving e (graphLaw (p ∘ edgeEquiv f)) (graphLaw p) :=
    measurePreserving_piCongrLeft (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (p i)) (edgeEquiv f)
  have hpre : e.symm ⁻¹' (exactOrderEvent (α := α) k)ᶜ = (exactOrderEvent (α := β) k)ᶜ := by
    ext w
    change (w ∘ edgeEquiv f ∉ exactOrderEvent k) ↔ (w ∉ exactOrderEvent k)
    exact not_congr (exactOrderEvent_reindex_iff f w k)
  rw [measureReal_def, measureReal_def, ← (hmap.symm e).measure_preimage
    (measurableSet_exactOrderEvent k).compl.nullMeasurableSet, hpre]

theorem atLeastOrderEvent_mono {k l : ℕ} (hkl : k ≤ l) :
    (atLeastOrderEvent l : Set (Edge α → ℝ)) ⊆ atLeastOrderEvent k := by
  intro w hw
  obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hw
  exact Set.mem_iUnion.mpr ⟨⟨S.val, hkl.trans S.property⟩, hS⟩

theorem exactOrderEvent_subset_atLeastOrderEvent {k l : ℕ} (hkl : k ≤ l) :
    (exactOrderEvent l : Set (Edge α → ℝ)) ⊆ atLeastOrderEvent k := by
  intro w hw
  obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hw
  exact Set.mem_iUnion.mpr ⟨⟨S.val, hkl.trans_eq S.property.symm⟩, hS⟩

theorem measurableSet_atLeastOrderEvent (k : ℕ) :
    MeasurableSet (atLeastOrderEvent (α := α) k) := by
  rw [atLeastOrderEvent_eq_iUnion_exactOrderEvent]
  exact MeasurableSet.iUnion (fun _ ↦ MeasurableSet.iUnion (fun _ ↦ measurableSet_exactOrderEvent _))

theorem probability_atLeastOrder_failure_reindex
    (f : α ≃o β) (p : Edge β → Icc (0 : ℝ) 1) (k : ℕ) :
    (graphLaw (p ∘ edgeEquiv f)).real (atLeastOrderEvent k)ᶜ =
      (graphLaw p).real (atLeastOrderEvent k)ᶜ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Edge β ↦ ℝ) (edgeEquiv f)
  have hmap : MeasurePreserving e (graphLaw (p ∘ edgeEquiv f)) (graphLaw p) :=
    measurePreserving_piCongrLeft (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (p i)) (edgeEquiv f)
  have hpre : e.symm ⁻¹' (atLeastOrderEvent (α := α) k)ᶜ = (atLeastOrderEvent (α := β) k)ᶜ := by
    ext w
    change (w ∘ edgeEquiv f ∉ atLeastOrderEvent k) ↔ (w ∉ atLeastOrderEvent k)
    apply not_congr
    rw [atLeastOrderEvent_eq_iUnion_exactOrderEvent, atLeastOrderEvent_eq_iUnion_exactOrderEvent,
      Fintype.card_congr f.toEquiv]
    simp only [Set.mem_iUnion, exactOrderEvent_reindex_iff f w]
  rw [measureReal_def, measureReal_def, ← (hmap.symm e).measure_preimage
    (measurableSet_atLeastOrderEvent k).compl.nullMeasurableSet, hpre]

theorem induce_preimage_atLeastOrder_subset (S : Finset α) (k : ℕ) :
    induce S ⁻¹' (atLeastOrderEvent (α := ↥S) k) ⊆ atLeastOrderEvent (α := α) k := by
  intro w hw
  change induce S w ∈ atLeastOrderEvent k at hw
  rw [atLeastOrderEvent_eq_iUnion_exactOrderEvent] at hw
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hw
  obtain ⟨hl', hw'⟩ := Set.mem_iUnion.mp hl
  exact exactOrderEvent_subset_atLeastOrderEvent (Finset.mem_Icc.mp hl').1
    (induce_preimage_exactOrder_subset S l hw')

theorem probability_exactOrder_failure_le_induced (p : Edge α → Icc (0 : ℝ) 1) (S : Finset α) (k : ℕ) :
    (graphLaw p).real (exactOrderEvent k)ᶜ ≤ (graphLaw (induce S p)).real (exactOrderEvent k)ᶜ := by
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  rw [measureReal_def, measureReal_def, ← (measurePreserving_induce p S).measure_preimage
    (measurableSet_exactOrderEvent k).compl.nullMeasurableSet]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (Set.compl_subset_compl.mpr (induce_preimage_exactOrder_subset S k))

theorem sampleRowMean_univ_eq_degree (w : Edge α → ℝ) (hα : 1 ≤ Fintype.card α) (i : α) :
    sampleRowMean Finset.univ (symmetricEdgeWeight w) i =
      degreeSum w i / ((Fintype.card α : ℝ) - 1) := by
  classical
  let f : ↥(Finset.univ : Finset α) ≃o α :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, Finset.mem_univ x⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  let j : ↥(Finset.univ : Finset α) := ⟨i, Finset.mem_univ _⟩
  have h := degreeSum_induce_eq_sum_erase Finset.univ w j
  have he : induce Finset.univ w = w ∘ edgeEquiv f := by funext e; rfl
  rw [he, degreeSum_reindex f] at h
  unfold sampleRowMean
  rw [Finset.card_univ, Nat.cast_sub hα, Nat.cast_one]
  congr 1
  exact h.symm

theorem arrayDensity_eq_normalized_vertexMean (p : Edge α → Icc (0 : ℝ) 1) :
    arrayDensity p = vertexMean (degreeSum (fun e ↦ (p e : ℝ))) / ((Fintype.card α : ℝ) - 1) := by
  have h := weighted_degree_sum (fun e ↦ (p e : ℝ)) (fun _ ↦ (1 : ℝ))
  simp only [one_add_one_eq_two, one_mul, ← Finset.mul_sum] at h
  unfold arrayDensity vertexMean
  rw [h, div_div]

end BoundedEdgeRegularSubgraphs
