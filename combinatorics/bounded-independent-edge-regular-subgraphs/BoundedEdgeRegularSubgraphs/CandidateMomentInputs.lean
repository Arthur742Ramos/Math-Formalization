module

public import BoundedEdgeRegularSubgraphs.CandidateSets
public import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# Candidate degree events and their local potentials
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The candidate-family estimates in terms of the actual vertex indices
of each induced array. -/
theorem eventually_exists_candidate_family_local {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ δ a₀ C : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < a₀ ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ N ≥ k, ∀ (q : Edge (Fin N) → Icc (0 : ℝ) 1) (p a η : ℝ),
        (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
        p ∈ Icc ξ (1 - ξ) → 0 ≤ a → a ≤ a₀ →
        let w := symmetricEdgeWeight (fun e ↦ (q e : ℝ))
        (∀ i, |sampleRowMean Finset.univ w i - p| ≤ a) →
        (∑ i, (sampleRowMean Finset.univ w i - p) ^ 2) ≤ (N : ℝ) * η ^ 2 →
        ∃ (d : ℤ) (F : Finset (Finset (Fin N))), Even ((k : ℤ) * d) ∧
          0 ≤ d ∧ d ≤ (k : ℤ) - 1 ∧ |(d : ℝ) - p * ((k : ℝ) - 1)| ≤ 1 ∧
          (N.choose k : ℝ) / 2 ≤ (F.card : ℝ) ∧
          ∀ S ∈ F, S.card = k ∧ ∃ θ : S → ℝ,
            (∀ i, (d : ℝ) = degreeSum (fun e ↦ (vertexTilt (induce S q) θ e : ℝ)) i) ∧
            (∀ e, δ ≤ (vertexTilt (induce S q) θ e : ℝ) ∧
              (vertexTilt (induce S q) θ e : ℝ) ≤ 1 - δ) ∧
            (∀ i, |θ i| ≤ C * (a + candidateDriftRate k)) ∧
            (∑ i, θ i ^ 2) ≤ C * (1 + η ^ 2 * k) ∧
            Real.exp (-(k : ℝ) / 2 * Real.log k - C * ((k : ℝ) + η ^ 2 * (k : ℝ) ^ 2)) ≤
              (graphLaw q).real (inducedDegreeAtom S d) := by
  obtain ⟨δ, a₀, C, hδ, hδ₁, ha₀, hC, h⟩ := eventually_exists_candidate_family hξ hξ₁
  refine ⟨δ, a₀, C, hδ, hδ₁, ha₀, hC, ?_⟩
  filter_upwards [h] with k hk
  intro N hN q p a η hq hp ha ha' w hα hη
  obtain ⟨d, F, hEven, hd₀, hd₁, hd, hcard, hFamily⟩ := hk N hN q p a η hq hp ha ha' hα hη
  refine ⟨d, F, hEven, hd₀, hd₁, hd, hcard, ?_⟩
  intro S hS
  obtain ⟨hSk, θ, hD, hFloor, hNorm, hEnergy, hpS⟩ := hFamily S hS
  let f := S.orderIsoOfFin hSk
  let ψ := θ ∘ f.symm
  let qS := induce S q
  have hShift : vertexTilt (qS ∘ edgeEquiv f) θ = vertexTilt qS ψ ∘ edgeEquiv f := by
    funext e
    change tiltProb (qS (edgeEquiv f e)) (θ e.val.1 + θ e.val.2) =
      tiltProb (qS (edgeEquiv f e)) (θ (f.symm (f e.val.1)) + θ (f.symm (f e.val.2)))
    rw [f.symm_apply_apply, f.symm_apply_apply]
  refine ⟨hSk, ψ, ?_, ?_, ?_, ?_, hpS⟩
  · intro i
    have he := congrFun hD (f.symm i)
    change degreeSum (fun e ↦ (vertexTilt (qS ∘ edgeEquiv f) θ e : ℝ)) (f.symm i) = (d : ℝ) at he
    simp_rw [hShift] at he
    change degreeSum ((fun e ↦ (vertexTilt qS ψ e : ℝ)) ∘ edgeEquiv f) (f.symm i) = (d : ℝ) at he
    rw [degreeSum_reindex f, f.apply_symm_apply] at he
    exact he.symm
  · intro e
    let e' := (edgeEquiv f).symm e
    have he := hFloor e'
    change δ ≤ (vertexTilt (qS ∘ edgeEquiv f) θ e' : ℝ) ∧
      (vertexTilt (qS ∘ edgeEquiv f) θ e' : ℝ) ≤ 1 - δ at he
    rw [hShift] at he
    simpa only [Function.comp_apply, e', Equiv.apply_symm_apply] using he
  · intro i
    change |θ (f.symm i)| ≤ _
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ _).trans hNorm
  · have he := f.symm.toEquiv.sum_comp (fun i ↦ θ i ^ 2)
    exact he.le.trans hEnergy

/-- On the support of the graph law, the failure of exact-order
regularity implies failure of every fixed-degree candidate of that size. -/
theorem probability_exactOrder_failure_le_no_candidate {n k : ℕ}
    (p : Edge (Fin n) → Icc (0 : ℝ) 1) (d : ℤ) (F : Finset (Finset (Fin n)))
    (hF : ∀ S ∈ F, S.card = k) :
    (graphLaw p).real (exactOrderEvent k)ᶜ ≤
      (graphLaw p).real (⋂ S ∈ F, (inducedDegreeAtom S d)ᶜ) := by
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  simp only [measureReal_def]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [graphLaw_ae_binary p] with w hw hFail
  simp only [mem_iInter, mem_compl_iff]
  intro S hS hAt
  apply hFail
  apply mem_iUnion.mpr
  refine ⟨⟨S, hF S hS⟩, ?_⟩
  change ∀ i j : S, degreeSum (induce S w) i = degreeSum (induce S w) j
  intro i j
  have hW (e : Edge ↥S) : induce S w e = 0 ∨ induce S w e = 1 := hw (inducedEdge S e)
  have hAt' : degreeVector Finset.univ (induce S w) = (fun _ : S ↦ d) := hAt
  rw [← degreeVector_univ_eq_degreeSum _ hW, ← degreeVector_univ_eq_degreeSum _ hW, hAt']

end BoundedEdgeRegularSubgraphs
