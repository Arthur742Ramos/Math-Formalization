module

public import BoundedEdgeRegularSubgraphs.OverlapReindex
public import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Partitioning by the binary configuration on the overlap
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Real edge data for a binary assignment on the shared clique. -/
noncomputable def binaryOverlap (S : Finset α) (b : edgesInside S → Bool) (e : Edge α) : ℝ := by
  classical
  exact if he : e ∈ edgesInside S then (if b ⟨e, he⟩ then 1 else 0) else 0

theorem binaryOverlap_binary (S : Finset α) (b : edgesInside S → Bool) (e : Edge α) :
    binaryOverlap S b e = 0 ∨ binaryOverlap S b e = 1 := by
  unfold binaryOverlap
  split_ifs <;> simp

private theorem overlapAssignment_pairwise_disjoint (S : Finset α) :
    Pairwise (fun b c : edgesInside S → Bool ↦
      Disjoint (overlapAssignmentEvent S (binaryOverlap S b))
        (overlapAssignmentEvent S (binaryOverlap S c))) := by
  classical
  intro b c hne
  apply Set.disjoint_left.mpr
  intro w hb hc
  apply hne
  funext e
  have hEq := (hb e.val e.property).symm.trans (hc e.val e.property)
  have he : binaryOverlap S b e.val = binaryOverlap S c e.val := hEq
  simp only [binaryOverlap, dif_pos e.property] at he
  cases hb' : b e <;> cases hc' : c e <;> simp_all

private theorem exists_binaryOverlap_of_binary (S : Finset α) (w : Edge α → ℝ)
    (hw : ∀ e, w e = 0 ∨ w e = 1) :
    ∃ b : edgesInside S → Bool, w ∈ overlapAssignmentEvent S (binaryOverlap S b) := by
  classical
  refine ⟨fun e ↦ decide (w e.val = 1), ?_⟩
  intro e he
  rcases hw e with h | h <;> simp [binaryOverlap, he, h]

/-- A measurable event is the sum of its probabilities on the finitely
many shared assignments. -/
theorem probability_sum_overlapAssignment (p : Edge α → Icc (0 : ℝ) 1)
    (S : Finset α) (E : Set (Edge α → ℝ)) (hE : MeasurableSet E) :
    (graphLaw p).real E = (by
      classical
      exact ∑ b : edgesInside S → Bool,
        (graphLaw p).real (E ∩ overlapAssignmentEvent S (binaryOverlap S b))) := by
  classical
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  let H (b : edgesInside S → Bool) := overlapAssignmentEvent S (binaryOverlap S b)
  have hC : E =ᵐ[graphLaw p] ⋃ b, E ∩ H b := by
    filter_upwards [graphLaw_ae_binary p] with w hw
    apply propext
    constructor
    · intro h
      obtain ⟨b, hb⟩ := exists_binaryOverlap_of_binary S w hw
      exact mem_iUnion.mpr ⟨b, h, hb⟩
    · intro h
      obtain ⟨b, hE', hH'⟩ := mem_iUnion.mp h
      exact hE'
  have hD : Pairwise (fun b c ↦ Disjoint (E ∩ H b) (E ∩ H c)) := by
    intro b c hne
    exact (overlapAssignment_pairwise_disjoint S hne).mono inter_subset_right inter_subset_right
  have hM (b : edgesInside S → Bool) : MeasurableSet (E ∩ H b) :=
    hE.inter (measurableSet_overlapAssignmentEvent _ _)
  rw [measureReal_congr hC, measureReal_iUnion_fintype hD hM]

/-- Integrating any function constant on the shared fibres is equivalent
to its probability-weighted sum over the binary assignments. -/
theorem integral_eq_sum_binaryOverlap {p : Edge α → Icc (0 : ℝ) 1}
    (S : Finset α) (f : (Edge α → ℝ) → ℝ)
    (hf : ∀ w h : Edge α → ℝ, w ∈ overlapAssignmentEvent S h → f w = f h) :
    (∫ w, f w ∂graphLaw p) = (by
      classical
      exact ∑ b : edgesInside S → Bool,
        (graphLaw p).real (overlapAssignmentEvent S (binaryOverlap S b)) * f (binaryOverlap S b)) := by
  classical
  let μ := graphLaw p
  have : IsProbabilityMeasure μ := by unfold μ graphLaw; infer_instance
  let H (b : edgesInside S → Bool) := overlapAssignmentEvent S (binaryOverlap S b)
  let g (b : edgesInside S → Bool) := (H b).indicator (fun _ ↦ f (binaryOverlap S b))
  have hM (b : edgesInside S → Bool) : MeasurableSet (H b) := measurableSet_overlapAssignmentEvent _ _
  have he : f =ᵐ[μ] fun w ↦ ∑ b, g b w := by
    filter_upwards [graphLaw_ae_binary p] with w hw
    obtain ⟨b, hb⟩ := exists_binaryOverlap_of_binary S w hw
    rw [Finset.sum_eq_single b]
    · change f w = (H b).indicator (fun _ ↦ f (binaryOverlap S b)) w
      rw [indicator_of_mem hb, hf w (binaryOverlap S b) hb]
    · intro c hc hne
      apply indicator_of_notMem
      exact fun h ↦ (Set.disjoint_left.mp (overlapAssignment_pairwise_disjoint S hne.symm)) hb h
    · simp
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    change (∫ w, (H b).indicator (fun _ ↦ f (binaryOverlap S b)) w ∂μ) = _
    rw [integral_indicator (hM b), setIntegral_const, smul_eq_mul]
  · intro b _
    exact (integrable_const _).indicator (hM b)

end BoundedEdgeRegularSubgraphs
