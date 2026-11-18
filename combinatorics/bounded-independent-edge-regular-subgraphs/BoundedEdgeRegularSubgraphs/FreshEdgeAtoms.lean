module

public import BoundedEdgeRegularSubgraphs.OverlapConditioning
public import BoundedEdgeRegularSubgraphs.ScalarAtoms
import Mathlib.MeasureTheory.Constructions.Pi
import BoundedEdgeRegularSubgraphs.PrefixProduct
import Mathlib.Tactic

/-!
# Independent edges from the shared vertices to the unshared vertices
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private abbrev Outside (S : Finset α) := ↥((Finset.univ : Finset α) \ S)

private theorem outside_notMem {S : Finset α} (j : Outside S) : (j : α) ∉ S :=
  (Finset.mem_sdiff.mp j.property).2

private def crossEdge {S : Finset α} (i : S) (j : Outside S) : Edge α :=
  ⟨(min (i : α) j, max (i : α) j), min_lt_max.2 (fun h ↦ outside_notMem j (h ▸ i.property))⟩

private theorem crossEdge_injective (S : Finset α) :
    Function.Injective (fun e : Σ _ : ↥S, Outside S ↦ crossEdge e.1 e.2) := by
  intro ⟨i, j⟩ ⟨i', j'⟩ h
  have hj : (j : α) ∉ S := outside_notMem j
  have hj' : (j' : α) ∉ S := outside_notMem j'
  have h₁ := congrArg (fun e : Edge α ↦ e.val.1) h
  have h₂ := congrArg (fun e : Edge α ↦ e.val.2) h
  change min (i : α) (j : α) = min (i' : α) (j' : α) at h₁
  change max (i : α) (j : α) = max (i' : α) (j' : α) at h₂
  rcases le_total (i : α) j with hij | hji <;> rcases le_total (i' : α) j' with hij' | hji'
  · rw [min_eq_left hij, min_eq_left hij'] at h₁
    rw [max_eq_right hij, max_eq_right hij'] at h₂
    congr 1 <;> exact Subtype.ext (by assumption)
  · rw [min_eq_left hij, min_eq_right hji'] at h₁
    exact (hj' (h₁ ▸ i.property)).elim
  · rw [min_eq_right hji, min_eq_left hij'] at h₁
    exact (hj (h₁.symm ▸ i'.property)).elim
  · rw [min_eq_right hji, min_eq_right hji'] at h₁
    rw [max_eq_left hji, max_eq_left hji'] at h₂
    congr 1 <;> exact Subtype.ext (by assumption)

private def freshRows (S : Finset α) (x : Edge α → ℝ) (i : S) (j : Outside S) : ℝ :=
  x (crossEdge i j)

private theorem measurePreserving_freshRows (p : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) :
    MeasurePreserving (freshRows S) (graphLaw p)
      (Measure.pi fun i : S ↦ bernoulliProduct (fun j : Outside S ↦ p (crossEdge i j))) := by
  let E (e : Σ _ : ↥S, Outside S) := crossEdge e.1 e.2
  let Y (x : Edge α → ℝ) (e : Σ _ : ↥S, Outside S) := x (E e)
  have hm (e : Σ _ : ↥S, Outside S) : Measurable (fun x ↦ Y x e) :=
    measurable_pi_apply (E e)
  have hind : iIndepFun (fun (e : Edge α) (x : Edge α → ℝ) ↦ x e) (graphLaw p) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  let μ (e : Σ _ : ↥S, Outside S) := bernoulliMeasure (1 : ℝ) 0 (p (E e))
  have hY : MeasurePreserving Y (graphLaw p) (Measure.pi μ) := by
    refine ⟨measurable_pi_iff.mpr hm, ?_⟩
    rw [(hind.precomp (crossEdge_injective S)).map_fun_eq_pi_map (fun e ↦ (hm e).aemeasurable)]
    congr 1
    funext e
    exact (measurePreserving_eval (fun e ↦ bernoulliMeasure (1 : ℝ) 0 (p e)) (E e)).map_eq
  exact (measurePreserving_piCurry (fun (_ : S) (_ : Outside S) ↦ ℝ)
    (fun i j ↦ μ ⟨i, j⟩)).comp hY

private theorem degreeVector_outside_eq_fresh_count (S : Finset α) (i : S) (x : Edge α → ℝ) :
    degreeVector (edgesOutsideOverlap S) x i = bernoulliCount (freshRows S x i) := by
  classical
  let A := (edgesOutsideOverlap S).filter fun e ↦ (i : α) = e.val.1 ∨ (i : α) = e.val.2
  have hh : degreeVector (edgesOutsideOverlap S) x i = ∑ e ∈ A, sampledIncidence e (x e) i := by
    simp only [degreeVector, Finset.sum_apply, A, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with h
    · rfl
    · have hf := not_or.mp h
      unfold sampledIncidence
      split_ifs <;> simp [edgeIncidence, hf.1, hf.2]
  rw [hh]
  symm
  unfold bernoulliCount
  refine Finset.sum_bij (fun j _ ↦ crossEdge i j) ?_ ?_ ?_ ?_
  · intro j _
    have hj := outside_notMem j
    rcases le_total (i : α) j with h | h
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Or.inl ?_⟩
      · exact fun hh ↦ hj (by simpa only [crossEdge, max_eq_right h] using hh.2)
      · simp only [crossEdge, min_eq_left h]
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Or.inr ?_⟩
      · exact fun hh ↦ hj (by simpa only [crossEdge, min_eq_right h] using hh.1)
      · simp only [crossEdge, max_eq_left h]
  · intro j _ j' _ h
    have he := crossEdge_injective S (a₁ := ⟨i, j⟩) (a₂ := ⟨i, j'⟩) h
    exact congrArg (fun e : Σ _ : ↥S, Outside S ↦ e.2) he
  · intro e he
    obtain ⟨hea, hi⟩ := Finset.mem_filter.mp he
    have hout := (Finset.mem_filter.mp hea).2
    rcases hi with h | h
    · have hj : e.val.2 ∉ S := fun hj ↦ hout ⟨h ▸ i.property, hj⟩
      refine ⟨⟨e.val.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change (min (i : α) e.val.2, max (i : α) e.val.2) = e.val
      rw [h, min_eq_left e.property.le, max_eq_right e.property.le]
    · have hj : e.val.1 ∉ S := fun hj ↦ hout ⟨hj, h ▸ i.property⟩
      refine ⟨⟨e.val.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      change (min (i : α) e.val.1, max (i : α) e.val.1) = e.val
      rw [h, min_eq_right e.property.le, max_eq_left e.property.le]
  · intro j _
    have hne : (i : α) ≠ (j : α) := fun h ↦ outside_notMem j (h ▸ i.property)
    have hinc : edgeIncidence (crossEdge i j) i = 1 := by
      rcases le_total (i : α) j with h | h
      · simp [edgeIncidence, crossEdge, min_eq_left h, max_eq_right h, hne]
      · simp [edgeIncidence, crossEdge, min_eq_right h, max_eq_left h, hne]
    change (if x (crossEdge i j) = 1 then 1 else 0) = sampledIncidence (crossEdge i j)
      (x (crossEdge i j)) i
    unfold sampledIncidence
    split_ifs <;> simp [hinc]

/-- A residual degree atom imposes one independent scalar constraint per
shared vertex, each on its edges to the unshared vertices. -/
theorem probability_residual_degreeAtom_le_fresh_edges (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ (S : Finset α) (d : α → ℤ),
      (graphLaw p).real (degreeAtom (edgesOutsideOverlap S) d) ≤
        (C / Real.sqrt ((Fintype.card α - S.card : ℕ) + 1)) ^ S.card := by
  classical
  obtain ⟨C, hC, hscalar⟩ := probability_countAtom_le_inv_sqrt ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro p hp S d
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  let P (i : S) := bernoulliProduct fun j : Outside S ↦ p (crossEdge i j)
  let U : Set ((i : S) → Outside S → ℝ) := Set.pi Set.univ fun i ↦ countAtom (d i)
  let b := C / Real.sqrt ((Fintype.card (Outside S) : ℝ) + 1)
  have hm : Measurable (bernoulliCount (ι := Outside S)) := by
    unfold bernoulliCount
    exact Finset.measurable_sum _ (fun i _ ↦ Measurable.ite
      ((measurableSet_singleton (1 : ℝ)).preimage (measurable_pi_apply i))
      measurable_const measurable_const)
  have hU : MeasurableSet U := MeasurableSet.pi Set.countable_univ
    (fun i _ ↦ measurableSet_eq_fun hm measurable_const)
  have hsub : degreeAtom (edgesOutsideOverlap S) d ⊆ freshRows S ⁻¹' U := by
    intro x hx
    change degreeVector (edgesOutsideOverlap S) x = d at hx
    apply Set.mem_pi.mpr
    intro i _
    change bernoulliCount (freshRows S x i) = d i
    rw [← degreeVector_outside_eq_fresh_count, hx]
  refine (measureReal_mono hsub).trans ?_
  have hpres := (measurePreserving_freshRows p S).measure_preimage hU.nullMeasurableSet
  change graphLaw p (freshRows S ⁻¹' U) = (Measure.pi P) U at hpres
  rw [measureReal_def, hpres]
  change ((Measure.pi P) (Set.pi Set.univ fun i ↦ countAtom (d i))).toReal ≤ _
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  have hb (i : S) : (P i).real (countAtom (d i)) ≤ b :=
    hscalar _ (fun j ↦ hp (crossEdge i j)) _
  calc
    _ ≤ ∏ _ : S, b := Finset.prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) (fun i _ ↦ hb i)
    _ = _ := by
      simp only [b, Finset.prod_const, Finset.card_univ, Outside, Fintype.card_coe,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

/-- The fresh-edge estimate after any overlap assignment of positive
probability. -/
theorem probability_conditional_degreeAtom_le_fresh_edges (ξ : ℝ)
    (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) →
      ∀ (S : Finset α) (h : Edge α → ℝ) (d : α → ℤ),
        0 < (graphLaw p).real (overlapAssignmentEvent S h) →
        (graphLaw p).real (degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h) /
          (graphLaw p).real (overlapAssignmentEvent S h) ≤
            (C / Real.sqrt ((Fintype.card α - S.card : ℕ) + 1)) ^ S.card := by
  obtain ⟨C, hC, hb⟩ := probability_residual_degreeAtom_le_fresh_edges (α := α) ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro p hp S h d hpos
  rw [probability_degreeAtom_given_overlap_eq p S h d hpos]
  exact hb p hp S (d - degreeVector (edgesInside S) h)

end BoundedEdgeRegularSubgraphs
