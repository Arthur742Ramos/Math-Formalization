/- AI-assisted formalization under the repository Apache-2.0 license.
Sparse global output preserves original intervals and zero residual floors. -/
module
public import ProtectedSources.RationalFloorSparsifyComplete
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_sparsify_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (e : ℚ) (he : 0 < e)
    (w v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hw : rationalFloorApproximation d s hs e=some w) (hv : rationalFloorSparsify d e w=some v) :
    ((fun a => (v.1 a : ℝ)),v.2.realData) ∈ floorIntervalGameClass d s (fun _ => 0) ∧
    (∀ a,response (intervalGameMatrix v.2.realData)
      (blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ))) a ≤ (v.2.bracket.2 : ℝ)) ∧
    (Finset.univ.filter fun i => v.2.q i ≠ 0).card ≤
      min m (k+rationalGridSize d.M (1-∑ a,v.1 a) e+1) := by
  obtain ⟨hp,hK,hD,hz,ha⟩ := rational_floor_sparsify_origin d e w v hv
  have hc := rational_floor_approximation_output_class d s (fun _ => 0) hs hR e w hw
  rcases hc with ⟨⟨hpa,hqa,hDI,hKI,hB,hBI⟩,hsp,_,hmass,hKs⟩
  have hsave := rational_sparse_gap_algorithm_sound w.2.K w.2.D w.1 d.M (1-∑ a,w.1 a)
    (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e (rationalUnconstrainedSystem m) v.2.q v.2.B ha
  have hg := hsave.2.1
  have hBnew := (residual_rat_real_iff v.2.q (rationalScore w.2.D w.1) d.M
    (w.2.bracket.2+e/((3 : ℕ) : ℚ)+e) v.2.B).mp hsave.2.2.1
  have hq0 : ∀ i,(0 : ℝ) ≤ (v.2.q i : ℝ) := fun i => by exact_mod_cast hg.1 i
  have hm : (∑ a,(w.1 a : ℝ))+(∑ i,(v.2.q i : ℝ))=1 := by
    have hh := hg.2.1
    have hhc : (∑ i,(v.2.q i : ℝ))=((1-∑ a,w.1 a : ℚ) : ℝ) := by exact_mod_cast hh
    push_cast at hhc
    linarith
  have hq1 : ∀ i,(v.2.q i : ℝ) ≤ 1 := by
    intro i
    have hi := Finset.single_le_sum (fun j _ => hq0 j) (Finset.mem_univ i)
    have hp0 : 0 ≤ ∑ a,(w.1 a : ℝ) := Finset.sum_nonneg fun a _ => hpa.1 a
    linarith
  have hClass : ((fun a => (v.1 a : ℝ)),v.2.realData) ∈ floorIntervalGameClass d s (fun _ => 0) := by
    change ((fun a => (v.1 a : ℝ)),((fun i => (v.2.q i : ℝ)),(fun i a => (v.2.D i a : ℝ)),
      (fun a b => (v.2.K a b : ℝ)),(fun i j => (v.2.B i j : ℝ)))) ∈ _
    rw [hp,hK,hD]
    exact ⟨⟨hpa,⟨hq0,hq1⟩,hDI,hKI,hBnew.1,hBnew.2.1⟩,hsp,(fun i => by simpa only [Rat.cast_zero] using hq0 i),hm,hKs⟩
  have hKq : ∀ a b,w.2.K a b= -w.2.K b a := by
    intro a b
    have hh := hKs a b
    change (w.2.K a b : ℝ)= -(w.2.K b a : ℝ) at hh
    exact_mod_cast hh
  have hKb : ∀ a b,-d.M ≤ w.2.K a b ∧ w.2.K a b ≤ d.M := by
    intro a b
    have hh : d.loK a b ≤ w.2.K a b ∧ w.2.K a b ≤ d.hiK a b := by
      exact_mod_cast (show (d.loK a b : ℝ) ≤ (w.2.K a b : ℝ) ∧
        (w.2.K a b : ℝ) ≤ (d.hiK a b : ℝ) from ⟨hKI.1 a b,hKI.2 a b⟩)
    exact ⟨le_trans (d.coreLower a b) hh.1,le_trans hh.2 (d.coreUpper a b)⟩
  have hDb : ∀ i a,-d.M ≤ w.2.D i a ∧ w.2.D i a ≤ d.M := by
    intro i a
    have hh : d.lo i a ≤ w.2.D i a ∧ w.2.D i a ≤ d.hi i a := by
      exact_mod_cast (show (d.lo i a : ℝ) ≤ (w.2.D i a : ℝ) ∧
        (w.2.D i a : ℝ) ≤ (d.hi i a : ℝ) from ⟨hDI.1 i a,hDI.2 i a⟩)
    exact ⟨le_trans (d.crossLower i a) hh.1,le_trans hh.2 (d.crossUpper i a)⟩
  have hfull := rational_sparse_gap_algorithm_full_game w.2.K w.2.D w.1 v.2.q d.M
    (1-∑ a,w.1 a) (w.2.bracket.2+e/((3 : ℕ) : ℚ)) e he
    (fun a => by
      have hh : (0 : ℝ) ≤ (w.1 a : ℝ) := hpa.1 a
      exact_mod_cast hh) (by ring) hKq hKb hDb (rationalUnconstrainedSystem m) v.2.B ha
  refine ⟨hClass,?_,?_⟩
  · simpa only [intervalGameMatrix,RationalIntervalRationalOutput.realData,hp,hK,hD,hz,Rat.cast_add] using hfull.2.2.2.2
  · simpa only [hp,Fintype.card_fin,Nat.add_zero] using hsave.2.2.2

end
end SparseCompletion
