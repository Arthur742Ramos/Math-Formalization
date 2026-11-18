module

public import BoundedEdgeRegularSubgraphs.InducedConditionalRatio
public import BoundedEdgeRegularSubgraphs.SharedRatioAveraging
import Mathlib.Tactic

/-!
# The averaged shared likelihood of two tilted candidates
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Regard the potential of an induced array as an ambient vertex function. -/
noncomputable def extendCandidateTilt (S : Finset α) (θ : S → ℝ) (i : α) : ℝ :=
  if hi : i ∈ S then θ ⟨i, hi⟩ else 0

noncomputable def sharedTiltWeight (q : Edge α → Icc (0 : ℝ) 1)
    (J : Finset α) (θ : α → ℝ) (w : Edge α → ℝ) : ℝ :=
  ∏ e ∈ edgesInside J, Real.exp ((θ e.val.1 + θ e.val.2) * w e) /
    tiltNormalizer (q e) (θ e.val.1 + θ e.val.2)

private theorem sharedTiltWeight_nonneg (q : Edge α → Icc (0 : ℝ) 1) (J : Finset α)
    (θ : α → ℝ) (w : Edge α → ℝ) : 0 ≤ sharedTiltWeight q J θ w :=
  Finset.prod_nonneg (fun e _ ↦ div_nonneg (Real.exp_nonneg _) (tiltNormalizer_pos _ _).le)

private theorem sharedTiltWeight_eq_on_assignment (q : Edge α → Icc (0 : ℝ) 1) (J : Finset α)
    (θ : α → ℝ) {w h : Edge α → ℝ} (hw : w ∈ overlapAssignmentEvent J h) :
    sharedTiltWeight q J θ w = sharedTiltWeight q J θ h := by
  unfold sharedTiltWeight
  exact Finset.prod_congr rfl (fun e he ↦ by rw [show w e = h e from hw e he])

private theorem candidate_sharedTiltWeight_eq_local (p : Edge α → Icc (0 : ℝ) 1)
    (S T : Finset α) (θ : S → ℝ) (h : Edge α → ℝ) :
    sharedTiltWeight p (S ∩ T) (extendCandidateTilt S θ) h =
      ∏ e ∈ edgesInside (overlapVertices S T),
        Real.exp ((θ e.val.1 + θ e.val.2) * (induce S h) e) /
          tiltNormalizer (induce S p e) (θ e.val.1 + θ e.val.2) := by
  unfold sharedTiltWeight
  rw [← map_edgesInside_overlapVertices S T, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  have h₁ : extendCandidateTilt S θ e.val.1.val = θ e.val.1 := by
    rw [extendCandidateTilt, dite_eq_left e.val.1.property]
  have h₂ : extendCandidateTilt S θ e.val.2.val = θ e.val.2 := by
    rw [extendCandidateTilt, dite_eq_left e.val.2.property]
  simp only [ambientInducedEdge, Function.Embedding.coeFn_mk, inducedEdge, h₁, h₂, induce]

private theorem conditional_candidate_ratio_le_of_tilted
    (p : Edge α → Icc (0 : ℝ) 1) (S T : Finset α) (θ : S → ℝ) (h : Edge α → ℝ) (d : ℤ)
    (hp : ∀ e, 0 < (p e : ℝ) ∧ (p e : ℝ) < 1)
    (hh : ∀ e, h e = 0 ∨ h e = 1)
    (hE : 0 < (graphLaw p).real (inducedDegreeAtom S d)) {a : ℝ}
    (hBound :
      let q := vertexTilt (induce S p) θ
      let H := overlapAssignmentEvent (overlapVertices S T) (induce S h)
      let E := degreeAtom Finset.univ (fun _ : S ↦ d)
      (((graphLaw q).real (E ∩ H) / (graphLaw q).real H) / (graphLaw q).real E) ≤ a) :
    let H := overlapAssignmentEvent (S ∩ T) h
    let E := inducedDegreeAtom S d
    (((graphLaw p).real (E ∩ H) / (graphLaw p).real H) / (graphLaw p).real E) ≤
      a * sharedTiltWeight p (S ∩ T) (extendCandidateTilt S θ) h := by
  let q := induce S p
  let J := overlapVertices S T
  let h' := induce S h
  let d' : S → ℤ := fun _ ↦ d
  have hqE : 0 < (graphLaw q).real (degreeAtom Finset.univ d') := by
    rwa [probability_inducedDegreeAtom_eq p S d] at hE
  have hqH : 0 < (graphLaw q).real (overlapAssignmentEvent J h') :=
    probability_overlapAssignment_pos q J h' (fun e _ ↦ hp (inducedEdge S e))
      (fun e _ ↦ hh (inducedEdge S e))
  have hchange := probability_degreeAtom_conditional_ratio_eq_shared_tilt q θ J h' d'
    (fun e _ ↦ hh (inducedEdge S e)) hqE hqH
  dsimp only
  rw [conditional_inducedDegreeAtom_ratio_eq p S T h d, hchange]
  rw [← candidate_sharedTiltWeight_eq_local p S T θ h]
  change (sharedTiltWeight p (S ∩ T) (extendCandidateTilt S θ) h) * _ ≤ _
  rw [mul_comm a]
  exact mul_le_mul_of_nonneg_left hBound (sharedTiltWeight_nonneg _ _ _ _)

/-- The moderate-overlap estimate of Lemma 3.1, with the stronger
coefficient on the restricted tilt energies used in Theorem 4.1. -/
theorem eventually_inducedDegreeAtom_sharedRatio_le {δ ρ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 2) (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      ∀ {α : Type*} [Fintype α] [LinearOrder α] (p : Edge α → Icc (0 : ℝ) 1),
        (∀ e, 0 < (p e : ℝ) ∧ (p e : ℝ) < 1) →
        ∀ (S T : Finset α), S.card = k → T.card = k →
        ∀ (θ : S → ℝ) (ψ : T → ℝ) (d : ℤ),
        Even ((k : ℤ) * d) →
        (∀ e, δ ≤ (vertexTilt (induce S p) θ e : ℝ) ∧ (vertexTilt (induce S p) θ e : ℝ) ≤ 1 - δ) →
        (∀ e, δ ≤ (vertexTilt (induce T p) ψ e : ℝ) ∧ (vertexTilt (induce T p) ψ e : ℝ) ≤ 1 - δ) →
        (∀ i, (d : ℝ) = degreeSum (fun e ↦ (vertexTilt (induce S p) θ e : ℝ)) i) →
        (∀ i, (d : ℝ) = degreeSum (fun e ↦ (vertexTilt (induce T p) ψ e : ℝ)) i) →
        0 < (graphLaw p).real (inducedDegreeAtom S d) →
        0 < (graphLaw p).real (inducedDegreeAtom T d) →
        let J := S ∩ T
        (J.card : ℝ) ≤ ρ * k →
        let U := ∑ i ∈ J, extendCandidateTilt S θ i ^ 2
        let V := ∑ i ∈ J, extendCandidateTilt T ψ i ^ 2
        (graphLaw p).real (inducedDegreeAtom S d ∩ inducedDegreeAtom T d) /
          ((graphLaw p).real (inducedDegreeAtom S d) * (graphLaw p).real (inducedDegreeAtom T d)) ≤
            C * Real.exp (D * (J.card : ℝ) ^ 2 / k + (J.card : ℝ) * (U + V) / 4) := by
  obtain ⟨K, hK, hConditional⟩ := eventually_probability_conditional_degreeAtom_ratio_finite hδ hδ₁ hρ hρ₁
  refine ⟨K ^ 2, 2 * K, by positivity, by positivity, ?_⟩
  filter_upwards [hConditional] with k hk
  intro α _ _ p hp S T hSk hTk θ ψ d hEven hθ hψ hdS hdT hES hET J hj
  let u := extendCandidateTilt S θ
  let v := extendCandidateTilt T ψ
  let a := K * Real.exp (K * (J.card : ℝ) ^ 2 / k)
  let L := sharedTiltWeight p J u
  let R := sharedTiltWeight p J v
  have ha : 0 ≤ a := mul_nonneg hK.le (Real.exp_nonneg _)
  have hParity {X : Finset α} (hX : X.card = k) : Even (∑ _ : X, d) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hX, nsmul_eq_mul] using hEven
  have hj' : ((overlapVertices S T).card : ℝ) ≤ ρ * k := by rwa [card_overlapVertices]
  have hj'' : ((overlapVertices T S).card : ℝ) ≤ ρ * k := by
    rwa [card_overlapVertices, Finset.inter_comm T S]
  have hmid := inducedDegreeAtom_joint_ratio_le_of_shared_bounds p S T d d ha L R
    (sharedTiltWeight_nonneg _ _ _) (sharedTiltWeight_nonneg _ _ _)
    (fun w h hw ↦ by
      dsimp only [L, R]
      rw [sharedTiltWeight_eq_on_assignment p J u hw, sharedTiltWeight_eq_on_assignment p J v hw])
    hES hET (fun b ↦ probability_overlapAssignment_pos p J _ (fun e _ ↦ hp e)
      (fun e _ ↦ binaryOverlap_binary J b e)) ?_ ?_
  · refine hmid.trans ?_
    have hon := integral_shared_tilt_likelihood_product_le (edgesInside J) p
      (fun e ↦ u e.val.1 + u e.val.2) (fun e ↦ v e.val.1 + v e.val.2)
    have hsum : (∑ e ∈ edgesInside J,
        ((u e.val.1 + u e.val.2) ^ 2 + (v e.val.1 + v e.val.2) ^ 2) / 8) ≤
        (J.card : ℝ) * ((∑ i ∈ J, u i ^ 2) + (∑ i ∈ J, v i ^ 2)) / 4 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      linarith only [sum_shared_tilt_shift_sq_le J u, sum_shared_tilt_shift_sq_le J v]
    refine (mul_le_mul_of_nonneg_left (hon.trans (Real.exp_le_exp.mpr hsum)) (sq_nonneg a)).trans_eq ?_
    dsimp only [a]
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring
  · intro b
    refine conditional_candidate_ratio_le_of_tilted p S T θ _ d hp (binaryOverlap_binary J b) hES ?_
    have h := hk (β := ↥S) ((Fintype.card_coe S).trans hSk) (overlapVertices S T)
      (vertexTilt (induce S p) θ) (induce S (binaryOverlap J b)) (fun _ ↦ d) hj' hθ
      (fun e _ ↦ binaryOverlap_binary J b (inducedEdge S e)) hdS (hParity hSk)
    simpa only [a, card_overlapVertices] using h
  · intro b
    have h := conditional_candidate_ratio_le_of_tilted p T S ψ (binaryOverlap J b) d hp
      (binaryOverlap_binary J b) hET (a := a) ?_
    · simpa only [Finset.inter_comm T S] using h
    · have ht := hk (β := ↥T) ((Fintype.card_coe T).trans hTk) (overlapVertices T S)
        (vertexTilt (induce T p) ψ) (induce T (binaryOverlap J b)) (fun _ ↦ d) hj'' hψ
        (fun e _ ↦ binaryOverlap_binary J b (inducedEdge T e)) hdT (hParity hTk)
      simpa only [a, card_overlapVertices, Finset.inter_comm T S] using ht

end BoundedEdgeRegularSubgraphs
