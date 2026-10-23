/- AI-assisted formalization under the repository Apache-2.0 license.
Global additive value approximation with actual sparse rational game output.
Specifications require zero residual floors. No polynomial cost claim. -/
module
public import ProtectedSources.RationalFloorSparsifyClass
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_floor_sparse_origin {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSparseApproximation d s hs ε=some v) :
    0 < ε ∧ ∃ w,rationalFloorApproximation d s hs (ε/((2 : ℕ) : ℚ))=some w ∧
      rationalFloorSparsify d (ε/((2 : ℕ) : ℚ)) w=some v := by
  by_cases he : 0 < ε
  · refine ⟨he,?_⟩
    cases hw : rationalFloorApproximation d s hs (ε/((2 : ℕ) : ℚ)) with
    | none => simp only [rationalFloorSparseApproximation,he,ite_true,hw,Option.bind_none] at hout; cases hout
    | some w =>
      exact ⟨w,rfl,by simpa only [rationalFloorSparseApproximation,he,ite_true,hw,Option.bind_some] using hout⟩
  · simp only [rationalFloorSparseApproximation,he,ite_false] at hout
    cases hout

theorem rational_floor_sparse_output_game {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ)
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSparseApproximation d s hs ε=some v) :
    ((fun a => (v.1 a : ℝ)),v.2.realData) ∈ floorIntervalGameClass d s (fun _ => 0) ∧
    (∀ a,response (intervalGameMatrix v.2.realData)
      (blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ))) a ≤ (v.2.bracket.2 : ℝ)) ∧
    (Finset.univ.filter fun i => v.2.q i ≠ 0).card ≤
      min m (k+rationalGridSize d.M (1-∑ a,v.1 a) (ε/((2 : ℕ) : ℚ))+1) := by
  obtain ⟨he,w,hw,hv⟩ := rational_floor_sparse_origin d s hs ε v hout
  exact rational_floor_sparsify_class d s hs hR _ (div_pos he (by norm_num)) w v hw hv

theorem rational_floor_sparse_global {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0))
    (hne : (floorIntervalGameClass d s (fun _ => 0)).Nonempty) (ε : ℚ) (hε : 0 < ε) :
    ∃ v : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalFloorSparseApproximation d s hs ε=some v ∧
      floorIntervalGameValue d s (fun _ => 0) ≤ (v.2.bracket.2 : ℝ) ∧
      (v.2.bracket.2 : ℝ) < floorIntervalGameValue d s (fun _ => 0)+(ε : ℝ) := by
  let e := ε/((2 : ℕ) : ℚ)
  have he : 0 < e := div_pos hε (by norm_num)
  obtain ⟨w,hw,hlo,hhi⟩ := rational_floor_approximation_global d s (fun _ => 0) hs
    (fun _ => le_rfl) hR hne e he
  obtain ⟨v,hv⟩ := rational_floor_sparsify_complete d s hs hR e he w hw
  have hz := (rational_floor_sparsify_origin d e w v hv).2.2.2.1
  have hu : (v.2.bracket.2 : ℝ)=(w.2.bracket.2 : ℝ)+(e : ℝ)/((3 : ℕ) : ℝ)+(e : ℝ) := by
    have hh := congrArg (fun z : ℚ × ℚ => (z.2 : ℝ)) hz
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast] using hh
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have heq : (e : ℝ)+(e : ℝ)=(ε : ℝ) := by
    dsimp only [e]
    push_cast
    ring
  refine ⟨v,?_,?_,?_⟩
  · dsimp only [e] at hw hv
    simp only [rationalFloorSparseApproximation,hε,ite_true,hw,Option.bind_some,hv]
  · rw [hu]
    linarith
  · rw [hu]
    linarith

theorem rational_floor_sparse_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ) (hε : 0 < ε) :
    rationalFloorSparseApproximation d s hs ε=none ↔ ¬(floorIntervalGameClass d s (fun _ => 0)).Nonempty := by
  constructor
  · intro hn hne
    let _ := floor_interval_class_nonempty_actions d s (fun _ => 0) hne
    obtain ⟨v,hv,_,_⟩ := rational_floor_sparse_global d s hs hR hne ε hε
    rw [hn] at hv
    cases hv
  · intro hn
    cases hv : rationalFloorSparseApproximation d s hs ε with
    | none => rfl
    | some v => exact False.elim (hn ⟨_,(rational_floor_sparse_output_game d s hs hR ε v hv).1⟩)

end SparseCompletion
