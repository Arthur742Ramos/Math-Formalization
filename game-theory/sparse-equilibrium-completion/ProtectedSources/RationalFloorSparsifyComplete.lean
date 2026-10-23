/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalFloorSparsify
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_floor_sparsify_complete {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (e : ℚ) (he : 0 < e)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorApproximation d s hs e=some w) :
    ∃ v,rationalFloorSparsify d e w=some v := by
  have hclass := rational_floor_approximation_output_class d s (fun _ => 0) hs hR e w hout
  rcases hclass with ⟨⟨_,hq,_,_,hB,hBI⟩,_,_,hmass,_⟩
  have hq' : ∀ i,(0 : ℝ) ≤ (w.2.q i : ℝ) := hq.1
  have hm : (∑ i,(w.2.q i : ℝ))=((1-∑ a,w.1 a : ℚ) : ℝ) := by
    push_cast
    change (∑ a,(w.1 a : ℝ))+(∑ i,(w.2.q i : ℝ))=1 at hmass
    linarith
  have hr := (rational_floor_approximation_rows d s hs e he w hout).2
  have hsys := exact_game_rational_gap_system_real w.2.K w.2.D w.1
    (fun i => (w.2.q i : ℝ)) (fun i j => (w.2.B i j : ℝ))
    d.M (1-∑ a,w.1 a) (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e d.positiveBound hq' hm hB hBI
    (by simpa only [intervalGameMatrix,RationalIntervalRationalOutput.realData,Rat.cast_add] using hr)
  have hnone : (rationalUnconstrainedSystem m).RealSatisfies (fun i => (w.2.q i : ℝ)) :=
    fun a => Fin.elim0 a
  obtain ⟨q,B,hqB⟩ := rational_sparse_gap_algorithm_complete w.2.K w.2.D w.1
    d.M (1-∑ a,w.1 a) (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e (rationalUnconstrainedSystem m)
    d.positiveBound he (fun i => (w.2.q i : ℝ))
    ((rational_linear_real_append_iff _ _ _).mpr ⟨hsys,hnone⟩) hq' hm
  exact ⟨(w.1,{ bracket := (0,w.2.bracket.2+e/((3 : ℕ) : ℚ)+e), q := q,
                K := w.2.K, D := w.2.D, B := B }),by
      simp only [rationalFloorSparsify,hqB,Option.map_some]⟩

end SparseCompletion
