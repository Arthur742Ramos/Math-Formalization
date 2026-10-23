/- AI-assisted formalization under the repository Apache-2.0 license.
Computed global value bracket from the proved additive upper certificate.
Zero residual floors only; no polynomial running-time assertion. -/
module
public import ProtectedSources.RationalFloorSparseDecision
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFloorSparseCertifiedApproximation {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  (rationalFloorSparseApproximation d s hs ε).map (fun w =>
    (w.1,{w.2 with bracket := (w.2.bracket.2-ε,w.2.bracket.2)}))

theorem rational_floor_sparse_certified_origin {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalFloorSparseCertifiedApproximation d s hs ε=some v) :
    ∃ w,rationalFloorSparseApproximation d s hs ε=some w ∧
      v=(w.1,{w.2 with bracket := (w.2.bracket.2-ε,w.2.bracket.2)}) := by
  cases hw : rationalFloorSparseApproximation d s hs ε with
  | none => simp only [rationalFloorSparseCertifiedApproximation,hw,Option.map_none] at hv; cases hv
  | some w =>
    refine ⟨w,rfl,?_⟩
    exact (Option.some.inj (by simpa only [rationalFloorSparseCertifiedApproximation,hw,Option.map_some] using hv)).symm

theorem rational_floor_sparse_certified_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ) (hε : 0 < ε) :
    rationalFloorSparseCertifiedApproximation d s hs ε=none ↔
      ¬(floorIntervalGameClass d s (fun _ => 0)).Nonempty := by
  rw [rationalFloorSparseCertifiedApproximation,Option.map_eq_none_iff,
    rational_floor_sparse_none_iff d s hs hR ε hε]

theorem rational_floor_sparse_certified_complete {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0))
    (hne : (floorIntervalGameClass d s (fun _ => 0)).Nonempty) (ε : ℚ) (hε : 0 < ε) :
    ∃ v,rationalFloorSparseCertifiedApproximation d s hs ε=some v := by
  obtain ⟨w,hw,_,_⟩ := rational_floor_sparse_global d s hs hR hne ε hε
  refine ⟨(w.1,{w.2 with bracket := (w.2.bracket.2-ε,w.2.bracket.2)}),?_⟩
  simp only [rationalFloorSparseCertifiedApproximation,hw,Option.map_some]

theorem rational_floor_sparse_certified_value {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ)
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalFloorSparseCertifiedApproximation d s hs ε=some v) :
    ((fun a => (v.1 a : ℝ)),v.2.realData) ∈ floorIntervalGameClass d s (fun _ => 0) ∧
    (∀ a,response (intervalGameMatrix v.2.realData)
      (blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ))) a ≤ (v.2.bracket.2 : ℝ)) ∧
    (v.2.bracket.1 : ℝ) < floorIntervalGameValue d s (fun _ => 0) ∧
    floorIntervalGameValue d s (fun _ => 0) ≤ (v.2.bracket.2 : ℝ) ∧
    v.2.bracket.2-v.2.bracket.1=ε ∧
    (Finset.univ.filter fun a =>
      blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ)) a ≠ 0).card ≤
      min (k+m) (((2 : ℕ))*k+rationalGridSize d.M (1-∑ a,v.1 a) (ε/((2 : ℕ) : ℚ))+1) := by
  obtain ⟨w,hw,rfl⟩ := rational_floor_sparse_certified_origin d s hs ε v hv
  have he := (rational_floor_sparse_origin d s hs ε w hw).1
  have hg := rational_floor_sparse_output_game d s hs hR ε w hw
  have hne : (floorIntervalGameClass d s (fun _ => 0)).Nonempty := ⟨_,hg.1⟩
  obtain ⟨w',hw',hlo,hhi⟩ := rational_floor_sparse_global d s hs hR hne ε he
  have heq : w'=w := Option.some.inj (hw'.symm.trans hw)
  subst w'
  refine ⟨hg.1,hg.2.1,?_,hlo,?_,rational_floor_sparse_total_support d s hs ε w hw⟩
  · change ((w.2.bracket.2-ε : ℚ) : ℝ) < _
    push_cast
    linarith
  · change w.2.bracket.2-(w.2.bracket.2-ε)=ε
    ring

end SparseCompletion
