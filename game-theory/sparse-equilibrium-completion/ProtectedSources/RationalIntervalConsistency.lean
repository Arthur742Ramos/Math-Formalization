/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalParameters
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem interval_pack_recovered_real {k m : ℕ} (lo hi V : Fin m → Fin k → ℚ)
    (K : Fin k → Fin k → ℚ) (q : Fin m → ℚ)
    (hV : ∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) :
    intervalPack (fun i => (q i : ℝ))
      (fun i a => (q i : ℝ)*(rationalIntervalRecover lo V q i a : ℝ))
      (fun a b => (K a b : ℝ)) (H := 0) Fin.elim0=
    fun j => (intervalPack (α := ℚ) q V K (H := 0) Fin.elim0 j : ℝ) := by
  have hprod := rational_interval_recovered_product lo hi V q hV
  funext j
  unfold intervalPack intervalVariableEncode
  generalize (rationalIntervalVariableEquiv k m 0).symm j=v
  rcases v with i | v
  · rfl
  · rcases v with v | v
    · change (q v.1 : ℝ)*(rationalIntervalRecover lo V q v.1 v.2 : ℝ)=(V v.1 v.2 : ℝ)
      exact_mod_cast hprod v.1 v.2
    · rcases v with v | v
      · rfl
      · exact Fin.elim0 v.1

theorem rational_interval_success_compatible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=some (x,B)) :
    d.Compatible := by
  obtain ⟨hpoint,hR,hB⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
    d.p d.M d.r d.M d.η d.R x B hout
  have hsave := hpoint
  obtain ⟨hq,hm,hV,hK,hKb,_⟩ := hsave
  have hD := (rational_interval_gap_recovered _ d.lo d.hi _ d.p _ d.M d.r d.M d.η d.orderedCross
    (rational_interval_point_gap d.loK d.hiK d.lo d.hi _ _ d.p _ d.M d.r d.M d.η _ hpoint).2.2).1
  have hbR := rational_residual_completion_real_sound (intervalQ (α := ℚ) x)
    (rationalScore (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x)) d.p) d.M (d.M+d.η) B hB
  refine ⟨(fun i => (intervalQ (α := ℚ) x i : ℝ)),(fun a b => (intervalK (α := ℚ) x a b : ℝ)),
    (fun i a => (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ)),
    (fun i j => (B i j : ℝ)),?_,?_,?_,?_,?_,hbR.1,hbR.2.1,?_⟩
  · intro i
    change (0 : ℝ) ≤ (intervalQ (α := ℚ) x i : ℝ)
    exact_mod_cast hq i
  · change (∑ i, (intervalQ (α := ℚ) x i : ℝ))=(d.r : ℝ)
    exact_mod_cast hm
  · intro a b
    change (intervalK (α := ℚ) x a b : ℝ)= -(intervalK (α := ℚ) x b a : ℝ)
    exact_mod_cast hK a b
  · intro a b
    change (d.loK a b : ℝ) ≤ (intervalK (α := ℚ) x a b : ℝ) ∧
      (intervalK (α := ℚ) x a b : ℝ) ≤ (d.hiK a b : ℝ)
    exact_mod_cast hKb a b
  · intro i a
    change (d.lo i a : ℝ) ≤ (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ∧
      (rationalIntervalRecover d.lo (intervalV (α := ℚ) x) (intervalQ (α := ℚ) x) i a : ℝ) ≤ (d.hi i a : ℝ)
    exact_mod_cast hD i a
  · rw [interval_pack_recovered_real d.lo d.hi (intervalV (α := ℚ) x) (intervalK (α := ℚ) x) (intervalQ (α := ℚ) x) hV]
    have hr := (rational_linear_real_cast_iff d.R (intervalPhysicalVector (α := ℚ) x)).mpr hR
    simpa only [interval_physical_projection] using hr

theorem rational_interval_compatible_success {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (h : d.Compatible) :
    ∃ x B, rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=some (x,B) := by
  let model := d.toModel h
  have hf := rational_interval_model_upper_feasible model
  apply rational_interval_repertoire_algorithm_real_complete d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R
    d.positiveBound d.positiveSlack d.orderedCross
  exact (rational_linear_real_feasible_iff _).mpr hf

end SparseCompletion
