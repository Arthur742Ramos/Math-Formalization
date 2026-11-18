module

public import BoundedEdgeRegularSubgraphs.Incidence
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact change of measure for a vertex tilt

The likelihood factor is first established on an individual binary outcome.
On a full degree atom the factor depends only on the specified degrees.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The normalizing factor of a Bernoulli log-odds update. -/
noncomputable def tiltNormalizer (q : Set.Icc (0 : ℝ) 1) (u : ℝ) : ℝ :=
  1 - (q : ℝ) + (q : ℝ) * Real.exp u

theorem tiltNormalizer_pos (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    0 < tiltNormalizer q u := by
  unfold tiltNormalizer
  by_cases h : (q : ℝ) = 0
  · simp [h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr q.property.2)
      (mul_pos (lt_of_le_of_ne q.property.1 (Ne.symm h)) (Real.exp_pos _))

/-- A Bernoulli probability after increasing its log-odds by u. -/
noncomputable def tiltProb (q : Set.Icc (0 : ℝ) 1) (u : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨(q : ℝ) * Real.exp u / tiltNormalizer q u, by
    refine ⟨div_nonneg (mul_nonneg q.property.1 (Real.exp_pos _).le)
      (tiltNormalizer_pos q u).le, ?_⟩
    rw [div_le_one (tiltNormalizer_pos q u)]
    exact le_add_of_nonneg_left (sub_nonneg.mpr q.property.2)⟩

private noncomputable def bitMass (q : Set.Icc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  if x = 1 then q else 1 - q

private theorem bitMass_tiltProb (q : Set.Icc (0 : ℝ) 1) (u x : ℝ) (hx : x = 0 ∨ x = 1) :
    bitMass (tiltProb q u) x =
      Real.exp (u * x - Real.log (tiltNormalizer q u)) * bitMass q x := by
  rw [Real.exp_sub, Real.exp_log (tiltNormalizer_pos q u)]
  rcases hx with hx | hx
  · subst x
    simp [bitMass, tiltProb]
    field_simp [(tiltNormalizer_pos q u).ne']
    simp [tiltNormalizer]
  · subst x
    simp [bitMass, tiltProb]
    ring

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The array after adding the two endpoint potentials to each log-odds. -/
noncomputable def vertexTilt (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) :
    Edge α → Set.Icc (0 : ℝ) 1 :=
  fun e ↦ tiltProb (q e) (θ e.val.1 + θ e.val.2)

/-- The log partition function of the vertex tilt. -/
noncomputable def logPartition (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) : ℝ :=
  ∑ e, Real.log (tiltNormalizer (q e) (θ e.val.1 + θ e.val.2))

private theorem real_graphLaw_singleton (q : Edge α → Set.Icc (0 : ℝ) 1)
    (w : Edge α → ℝ) (hw : ∀ e, w e = 0 ∨ w e = 1) :
    (graphLaw q).real {w} = ∏ e, bitMass (q e) (w e) := by
  rw [measureReal_def, graphLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure (1 : ℝ) 0 (q e)).real {w e} = bitMass (q e) (w e)
  rcases hw e with h | h <;> simp [bitMass, h]

/-- The exact likelihood identity on each graph, including zero-mass outcomes. -/
theorem real_graphLaw_vertexTilt_singleton (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (w : Edge α → ℝ) (hw : ∀ e, w e = 0 ∨ w e = 1) :
    (graphLaw (vertexTilt q θ)).real {w} =
      Real.exp ((∑ i, θ i * degreeSum w i) - logPartition q θ) * (graphLaw q).real {w} := by
  rw [real_graphLaw_singleton _ _ hw, real_graphLaw_singleton q _ hw]
  simp_rw [vertexTilt, fun e ↦ bitMass_tiltProb (q e) (θ e.val.1 + θ e.val.2) (w e) (hw e)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_sub_distrib, ← weighted_degree_sum]
  rfl

private noncomputable def encodeGraph (b : Edge α → Bool) : Edge α → ℝ :=
  fun e ↦ if b e then 1 else 0

omit [Fintype α] in
private theorem encodeGraph_injective : Function.Injective (encodeGraph (α := α)) := by
  intro b c h
  funext e
  have he := congrFun h e
  cases hb : b e <;> cases hc : c e <;> simp_all [encodeGraph]

omit [Fintype α] in
private theorem encodeGraph_binary (b : Edge α → Bool) (e : Edge α) :
    encodeGraph b e = 0 ∨ encodeGraph b e = 1 := by
  cases h : b e <;> simp [encodeGraph, h]

private theorem real_graphLaw_apply (q : Edge α → Set.Icc (0 : ℝ) 1)
    (s : Set (Edge α → ℝ)) :
    (graphLaw q).real s =
      (by
        classical
        exact ∑ b : Edge α → Bool,
          if encodeGraph b ∈ s then (graphLaw q).real {encodeGraph b} else 0) := by
  classical
  have : IsProbabilityMeasure (graphLaw q) := by unfold graphLaw; infer_instance
  let f (b : Edge α → Bool) : Set (Edge α → ℝ) :=
    if encodeGraph b ∈ s then {encodeGraph b} else ∅
  have hcover : s =ᵐ[graphLaw q] ⋃ b, f b := by
    filter_upwards [graphLaw_ae_binary q] with w hw
    apply propext
    constructor
    · intro hws
      let b : Edge α → Bool := fun e ↦ decide (w e = 1)
      have henc : encodeGraph b = w := by
        funext e
        rcases hw e with h | h <;> simp [encodeGraph, b, h]
      exact Set.mem_iUnion.mpr ⟨b, by simp [f, henc, hws]⟩
    · intro h
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
      by_cases hs : encodeGraph b ∈ s
      · have he : w = encodeGraph b := by simpa [f, hs] using hb
        simpa [he] using hs
      · simp [f, hs] at hb
  have hdis : Pairwise (fun b c ↦ Disjoint (f b) (f c)) := by
    intro b c hbc
    refine Set.disjoint_left.mpr (fun w hb hc ↦ ?_)
    by_cases hb' : encodeGraph b ∈ s
    · by_cases hc' : encodeGraph c ∈ s
      · have h₁ : w = encodeGraph b := by simpa [f, hb'] using hb
        have h₂ : w = encodeGraph c := by simpa [f, hc'] using hc
        exact hbc (encodeGraph_injective (h₁.symm.trans h₂))
      · simp [f, hc'] at hc
    · simp [f, hb'] at hb
  have hm (b : Edge α → Bool) : MeasurableSet (f b) := by
    by_cases h : encodeGraph b ∈ s <;> simp [f, h]
  rw [measureReal_congr hcover, measureReal_iUnion_fintype hdis hm]
  exact Finset.sum_congr rfl (fun b _ ↦ by by_cases h : encodeGraph b ∈ s <;> simp [f, h])

/-- The likelihood is constant on subevents of a full degree atom. -/
theorem real_graphLaw_vertexTilt_sub_degreeAtom (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (d : α → ℤ) (E : Set (Edge α → ℝ)) (hE : E ⊆ degreeAtom Finset.univ d) :
    (graphLaw (vertexTilt q θ)).real E =
      Real.exp ((∑ i, θ i * (d i : ℝ)) - logPartition q θ) *
        (graphLaw q).real E := by
  classical
  rw [real_graphLaw_apply, real_graphLaw_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : encodeGraph b ∈ E
  · simp only [ite_eq_left hb]
    rw [real_graphLaw_vertexTilt_singleton q θ _ (encodeGraph_binary b)]
    have hdeg (i : α) : degreeSum (encodeGraph b) i = (d i : ℝ) := by
      rw [← degreeVector_univ_eq_degreeSum _ (encodeGraph_binary b)]
      exact congrArg (fun f : α → ℤ ↦ (f i : ℝ))
        (show degreeVector Finset.univ (encodeGraph b) = d from hE hb)
    simp_rw [hdeg]
  · simp [hb]

/-- On a full degree atom the likelihood factor is constant. -/
theorem real_graphLaw_vertexTilt_degreeAtom (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (d : α → ℤ) :
    (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) =
      Real.exp ((∑ i, θ i * (d i : ℝ)) - logPartition q θ) *
        (graphLaw q).real (degreeAtom Finset.univ d) :=
  real_graphLaw_vertexTilt_sub_degreeAtom q θ d _ (fun _ hw ↦ hw)

private theorem real_graphLaw_specified_edges (q : Edge α → Set.Icc (0 : ℝ) 1)
    (A : Finset (Edge α)) (h : Edge α → ℝ) (hb : ∀ e ∈ A, h e = 0 ∨ h e = 1) :
    (graphLaw q).real {w | ∀ e ∈ A, w e = h e} = ∏ e ∈ A, bitMass (q e) (h e) := by
  classical
  have he : {w | ∀ e ∈ A, w e = h e} =
      Set.pi (A : Set (Edge α)) (fun e ↦ ({h e} : Set ℝ)) := by
    ext w
    simp [Set.mem_pi]
  rw [he, measureReal_def, graphLaw, Measure.pi_pi_finset, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e he'
  change (bernoulliMeasure (1 : ℝ) 0 (q e)).real {h e} = bitMass (q e) (h e)
  rcases hb e he' with hh | hh <;> simp [bitMass, hh]

/-- The likelihood factor of a partial binary assignment only contains
the log-odds increments on the specified edges. -/
theorem real_graphLaw_vertexTilt_specified_edges (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (A : Finset (Edge α)) (h : Edge α → ℝ)
    (hb : ∀ e ∈ A, h e = 0 ∨ h e = 1) :
    (graphLaw (vertexTilt q θ)).real {w | ∀ e ∈ A, w e = h e} =
      (∏ e ∈ A, Real.exp ((θ e.val.1 + θ e.val.2) * h e) /
        tiltNormalizer (q e) (θ e.val.1 + θ e.val.2)) *
      (graphLaw q).real {w | ∀ e ∈ A, w e = h e} := by
  rw [real_graphLaw_specified_edges _ A h hb, real_graphLaw_specified_edges q A h hb,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e he ↦ by
    let u := θ e.val.1 + θ e.val.2
    change bitMass (tiltProb (q e) u) (h e) =
      (Real.exp (u * h e) / tiltNormalizer (q e) u) * bitMass (q e) (h e)
    rw [bitMass_tiltProb _ _ _ (hb e he), Real.exp_sub, Real.exp_log (tiltNormalizer_pos _ _)])

/-- The centred Bernoulli log partition function is bounded by u²/8. -/
theorem logTiltNormalizer_sub_le (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    Real.log (tiltNormalizer q u) - (q : ℝ) * u ≤ u ^ 2 / 8 := by
  let P := bernoulliMeasure (1 : ℝ) 0 q
  have : IsProbabilityMeasure P := by unfold P; infer_instance
  have hsupp : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_iff.mpr (bernoulliMeasure_apply_of_notMem_of_notMem q measurableSet_Icc.compl
      (by simp) (by simp))
  have hmean : ∫ x, (id x : ℝ) ∂P = (q : ℝ) := by
    unfold P
    simpa using integral_bernoulliMeasure (1 : ℝ) 0 q id
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := id) aemeasurable_id hsupp
  rw [hmean] at hsub
  have hmgf := hsub.mgf_le u
  have hconst : ((↑(((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) : NNReal) : ℝ) * u ^ 2 / 2) =
      u ^ 2 / 8 := by
    push_cast
    norm_num
    ring
  rw [hconst, mgf] at hmgf
  change (∫ x, Real.exp (u * (x - (q : ℝ))) ∂P) ≤ Real.exp (u ^ 2 / 8) at hmgf
  unfold P at hmgf
  rw [integral_bernoulliMeasure] at hmgf
  apply Real.exp_le_exp.mp
  calc
    Real.exp (Real.log (tiltNormalizer q u) - (q : ℝ) * u) =
        (q : ℝ) • Real.exp (u * (1 - (q : ℝ))) +
          (1 - (q : ℝ)) • Real.exp (u * (0 - (q : ℝ))) := by
      rw [Real.exp_sub, Real.exp_log (tiltNormalizer_pos q u)]
      simp only [tiltNormalizer, smul_eq_mul, mul_sub, mul_one, zero_sub,
        Real.exp_sub]
      rw [mul_comm u (q : ℝ), mul_neg, Real.exp_neg]
      ring
    _ ≤ _ := hmgf

/-- The quadratic likelihood cost of a vertex tilt, before optimizing the potentials. -/
theorem logPartition_le_quadratic (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) :
    logPartition q θ ≤ (∑ i, θ i * degreeSum (fun e ↦ (q e : ℝ)) i) +
      (∑ e : Edge α, (θ e.val.1 + θ e.val.2) ^ 2) / 8 := by
  have h (e : Edge α) :
      Real.log (tiltNormalizer (q e) (θ e.val.1 + θ e.val.2)) -
          (θ e.val.1 + θ e.val.2) * (q e : ℝ) ≤
        (θ e.val.1 + θ e.val.2) ^ 2 / 8 := by
    rw [mul_comm (θ e.val.1 + θ e.val.2)]
    exact logTiltNormalizer_sub_le _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ ↦ h e)
  rw [Finset.sum_sub_distrib, ← weighted_degree_sum, ← Finset.sum_div] at hs
  unfold logPartition
  linarith only [hs]

/-- The original atom is bounded by its tilted mass times the quadratic cost. -/
theorem degreeAtom_original_le_tilted_cost (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (d : α → ℤ) :
    (graphLaw q).real (degreeAtom Finset.univ d) ≤
      Real.exp ((∑ i, θ i * degreeSum (fun e ↦ (q e : ℝ)) i) +
        (∑ e : Edge α, (θ e.val.1 + θ e.val.2) ^ 2) / 8 - (∑ i, θ i * (d i : ℝ))) *
        (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) := by
  calc
    _ = Real.exp (logPartition q θ - (∑ i, θ i * (d i : ℝ))) *
        (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) := by
      rw [real_graphLaw_vertexTilt_degreeAtom, ← mul_assoc, ← Real.exp_add]
      have h : (logPartition q θ - ∑ i, θ i * (d i : ℝ)) +
          ((∑ i, θ i * (d i : ℝ)) - logPartition q θ) = 0 := by ring
      rw [h, Real.exp_zero, one_mul]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (sub_le_sub_right
        (logPartition_le_quadratic q θ) _)) measureReal_nonneg

end BoundedEdgeRegularSubgraphs
