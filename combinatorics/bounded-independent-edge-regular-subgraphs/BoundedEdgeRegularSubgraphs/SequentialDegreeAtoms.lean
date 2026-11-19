module

public import BoundedEdgeRegularSubgraphs.ScalarAtoms
import BoundedEdgeRegularSubgraphs.PrefixProduct

/-!
# Sequential exposure of the degree constraints

The row at vertex i consists of its edges to later vertices. Earlier
rows contribute a fixed incoming count at each exposure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

abbrev ForwardVertex {n : ℕ} (i : Fin n) := {j : Fin n // i < j}

private def rowEdgeEquiv (n : ℕ) : (Σ i : Fin n, ForwardVertex i) ≃ Edge (Fin n) where
  toFun e := ⟨(e.1, e.2.val), e.2.property⟩
  invFun e := ⟨e.val.1, ⟨e.val.2, e.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {n : ℕ}

private def edgesFromRows (x : (i : Fin n) → ForwardVertex i → ℝ) (e : Edge (Fin n)) : ℝ :=
  x e.val.1 ⟨e.val.2, e.property⟩

private def rowsFromEdges (w : Edge (Fin n) → ℝ) (i : Fin n) (j : ForwardVertex i) : ℝ :=
  w ⟨(i, j.val), j.property⟩

private noncomputable def rowProbability (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1)
    (i : Fin n) (j : ForwardVertex i) : Set.Icc (0 : ℝ) 1 :=
  p ⟨(i, j.val), j.property⟩

private theorem measurePreserving_rows (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1) :
    MeasurePreserving rowsFromEdges (graphLaw p)
      (Measure.pi fun i ↦ bernoulliProduct (rowProbability p i)) := by
  let μ (e : Edge (Fin n)) := bernoulliMeasure (1 : ℝ) 0 (p e)
  have h₁ := measurePreserving_piCongrLeft μ (rowEdgeEquiv n)
  have h₂ := measurePreserving_piCurry (fun (i : Fin n) (_ : ForwardVertex i) ↦ ℝ)
    (fun i j ↦ μ (rowEdgeEquiv n ⟨i, j⟩))
  exact h₂.comp (MeasurePreserving.symm _ h₁)

private theorem measurable_edgesFromRows : Measurable (edgesFromRows (n := n)) := by
  apply measurable_pi_iff.mpr
  intro e
  let j : ForwardVertex e.val.1 := ⟨e.val.2, e.property⟩
  have hj : Measurable (fun w : ForwardVertex e.val.1 → ℝ ↦ w j) := measurable_pi_apply j
  exact hj.comp (measurable_pi_apply e.val.1)

private theorem degree_fromRows_prefix (i : Fin n) (x y : (j : Fin n) → ForwardVertex j → ℝ)
    (hxy : ∀ j, j ≤ i → x j = y j) :
    degreeVector Finset.univ (edgesFromRows x) i = degreeVector Finset.univ (edgesFromRows y) i := by
  classical
  simp only [degreeVector, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun e _ ↦ ?_)
  by_cases h₁ : i = e.val.1
  · simp only [edgesFromRows, hxy e.val.1 (le_of_eq h₁.symm)]
  · by_cases h₂ : i = e.val.2
    · have hle : e.val.1 ≤ i := by rw [h₂]; exact le_of_lt e.property
      simp only [edgesFromRows, hxy e.val.1 hle]
    · by_cases hx : edgesFromRows x e = 1 <;> by_cases hy : edgesFromRows y e = 1 <;>
        simp [sampledIncidence, edgeIncidence, h₁, h₂, hx, hy]

private theorem degree_fromRows_update (i : Fin n) (x : (j : Fin n) → ForwardVertex j → ℝ)
    (y : ForwardVertex i → ℝ) :
    degreeVector Finset.univ (edgesFromRows (Function.update x i y)) i =
      bernoulliCount y +
        ∑ e ∈ (Finset.univ.filter fun e : Edge (Fin n) ↦ e.val.1 ≠ i),
          sampledIncidence e (edgesFromRows x e) i := by
  classical
  let w := edgesFromRows (Function.update x i y)
  have ho : (bernoulliCount y : ℤ) =
      ∑ e ∈ (Finset.univ.filter fun e : Edge (Fin n) ↦ e.val.1 = i), sampledIncidence e (w e) i := by
    unfold bernoulliCount
    refine Finset.sum_bij (fun j _ ↦ (⟨(i, j.val), j.property⟩ : Edge (Fin n))) ?_ ?_ ?_ ?_
    · intro j _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · intro j _ j' _ hh
      exact Subtype.ext (congrArg (fun e : Edge (Fin n) ↦ e.val.2) hh)
    · intro e he
      have h₁ := (Finset.mem_filter.mp he).2
      have hlt : i < e.val.2 := by rw [← h₁]; exact e.property
      refine ⟨⟨e.val.2, hlt⟩, Finset.mem_univ _, ?_⟩
      exact Subtype.ext (Prod.ext h₁.symm rfl)
    · intro j _
      have hne : i ≠ j.val := ne_of_lt j.property
      change (if y j = 1 then (1 : ℤ) else 0) =
        sampledIncidence (⟨(i, j.val), j.property⟩ : Edge (Fin n))
          ((Function.update x i y) i j) i
      rw [Function.update_self]
      by_cases hj : y j = 1
      · simp [sampledIncidence, edgeIncidence, hj, hne]
      · simp [sampledIncidence, hj]
  have hi :
      (∑ e ∈ (Finset.univ.filter fun e : Edge (Fin n) ↦ e.val.1 ≠ i),
        sampledIncidence e (w e) i) =
      ∑ e ∈ (Finset.univ.filter fun e : Edge (Fin n) ↦ e.val.1 ≠ i),
        sampledIncidence e (edgesFromRows x e) i := by
    refine Finset.sum_congr rfl (fun e he ↦ ?_)
    have hne := (Finset.mem_filter.mp he).2
    simp only [w, edgesFromRows, Function.update_of_ne hne]
  change degreeVector Finset.univ w i = _
  simp only [degreeVector, Finset.sum_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : Edge (Fin n) ↦ e.val.1 = i) (fun e ↦ sampledIncidence e (w e) i), ← ho, hi]

/-- The sequential degree constraints cost at most the product of the scalar atom bounds. -/
theorem probability_degreeAtom_le_row_product (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1),
      (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) → ∀ d : Fin n → ℤ,
      (graphLaw p).real (degreeAtom Finset.univ d) ≤
        ∏ i : Fin n, C / Real.sqrt ((Fintype.card (ForwardVertex i) : ℝ) + 1) := by
  classical
  obtain ⟨C, hC, hscalar⟩ := probability_countAtom_le_inv_sqrt ξ hξ hξ'
  refine ⟨C, hC, ?_⟩
  intro n p hp d
  let rowLaw (i : Fin n) := bernoulliProduct (rowProbability p i)
  let a (i : Fin n) := C / Real.sqrt ((Fintype.card (ForwardVertex i) : ℝ) + 1)
  let good (i : Fin n) (x : (j : Fin n) → ForwardVertex j → ℝ) :=
    degreeVector Finset.univ (edgesFromRows x) i = d i
  have hmeas (i : Fin n) : MeasurableSet {x | good i x} := by
    exact measurableSet_eq_fun ((measurable_pi_apply i).comp
      ((measurable_degreeVector Finset.univ).comp measurable_edgesFromRows)) measurable_const
  have h := measure_pi_prefix_le n (fun i ↦ ForwardVertex i → ℝ) rowLaw good
    (fun i ↦ ENNReal.ofReal (a i)) hmeas (by
      intro i x y hxy
      unfold good
      rw [degree_fromRows_prefix i x y hxy]) (by
      intro i x
      let incoming := ∑ e ∈ (Finset.univ.filter fun e : Edge (Fin n) ↦ e.val.1 ≠ i),
        sampledIncidence e (edgesFromRows x e) i
      have hevent : {z | good i (Function.update x i z)} = countAtom (d i - incoming) := by
        ext y
        change degreeVector Finset.univ (edgesFromRows (Function.update x i y)) i = d i ↔
          bernoulliCount y = d i - incoming
        rw [degree_fromRows_update]
        exact eq_sub_iff_add_eq.symm
      rw [hevent]
      have hs := hscalar (rowProbability p i) (fun j ↦ hp ⟨(i, j.val), j.property⟩)
        (d i - incoming)
      have hb := ENNReal.ofReal_le_ofReal hs
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hb
      exact hb)
  have hpre : rowsFromEdges ⁻¹' {x | ∀ i, good i x} = degreeAtom Finset.univ d := by
    ext w
    change (∀ i, degreeVector Finset.univ (edgesFromRows (rowsFromEdges w)) i = d i) ↔
      degreeVector Finset.univ w = d
    exact funext_iff.symm
  have hall : MeasurableSet {x | ∀ i, good i x} := by
    have heq : {x | ∀ i, good i x} = ⋂ i, {x | good i x} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter hmeas
  rw [← (measurePreserving_rows p).measure_preimage hall.nullMeasurableSet, hpre] at h
  have hnontop : (∏ i, ENNReal.ofReal (a i)) ≠ (⊤ : ENNReal) := ENNReal.prod_ne_top (by simp)
  have hr := ENNReal.toReal_mono hnontop h
  rw [ENNReal.toReal_prod] at hr
  calc
    _ ≤ ∏ i, (ENNReal.ofReal (a i)).toReal := hr
    _ = _ := Finset.prod_congr rfl (fun _ _ ↦
      ENNReal.toReal_ofReal (div_nonneg hC.le (Real.sqrt_nonneg _)))

end BoundedEdgeRegularSubgraphs
