/- AI-assisted formalization under the repository Apache-2.0 license.
A returned global bracket for arbitrary nonnegative coordinate floors.
This retains the dense allocation-search witness, without a sparsity claim. -/
module
public import ProtectedSources.RationalSourceFloorRows
@[expose] public section
namespace SparseCompletion

def rationalSourceFloorCertifiedApproximation {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  (rationalSourceFloorApproximation d s hs ε).map (fun w =>
    (w.1,{w.2 with bracket := (w.2.bracket.2+ε/((3 : ℕ) : ℚ)-ε,w.2.bracket.2+ε/((3 : ℕ) : ℚ))}))

theorem rational_source_floor_certified_origin {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalSourceFloorCertifiedApproximation d s hs ε=some v) :
    0 < ε ∧ ∃ w,rationalSourceFloorApproximation d s hs ε=some w ∧
      v=(w.1,{w.2 with bracket := (w.2.bracket.2+ε/((3 : ℕ) : ℚ)-ε,w.2.bracket.2+ε/((3 : ℕ) : ℚ))}) := by
  have he : 0 < ε := by
    by_contra hh
    simp only [rationalSourceFloorCertifiedApproximation,rationalSourceFloorApproximation,dite_eq_right hh,
      Option.map_none] at hv
    cases hv
  refine ⟨he,?_⟩
  cases hw : rationalSourceFloorApproximation d s hs ε with
  | none => simp only [rationalSourceFloorCertifiedApproximation,hw,Option.map_none] at hv; cases hv
  | some w =>
    refine ⟨w,rfl,?_⟩
    exact (Option.some.inj (by simpa only [rationalSourceFloorCertifiedApproximation,hw,Option.map_some] using hv)).symm

theorem rational_source_floor_certified_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) :
    rationalSourceFloorCertifiedApproximation d s hs ε=none ↔ ¬(floorIntervalGameClass d s u).Nonempty := by
  rw [rationalSourceFloorCertifiedApproximation,Option.map_eq_none_iff,
    rational_source_floor_none_iff d s u hs hu hR ε hε]

theorem rational_source_floor_certified_complete {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty) (ε : ℚ) (hε : 0 < ε) :
    ∃ v,rationalSourceFloorCertifiedApproximation d s hs ε=some v := by
  obtain ⟨w,hw,_,_⟩ := rational_source_floor_approximation_global d s u hs hu hR hne ε hε
  refine ⟨(w.1,{w.2 with bracket := (w.2.bracket.2+ε/((3 : ℕ) : ℚ)-ε,w.2.bracket.2+ε/((3 : ℕ) : ℚ))}),?_⟩
  simp only [rationalSourceFloorCertifiedApproximation,hw,Option.map_some]

theorem rational_source_floor_certified_value {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalSourceFloorCertifiedApproximation d s hs ε=some v) :
    ((fun a => (v.1 a : ℝ)),v.2.realData) ∈ floorIntervalGameClass d s u ∧
    (∀ a,response (intervalGameMatrix v.2.realData)
      (blockWeights (fun a => (v.1 a : ℝ)) (fun i => (v.2.q i : ℝ))) a ≤ (v.2.bracket.2 : ℝ)) ∧
    (v.2.bracket.1 : ℝ) < floorIntervalGameValue d s u ∧
    floorIntervalGameValue d s u ≤ (v.2.bracket.2 : ℝ) ∧
    v.2.bracket.2-v.2.bracket.1=ε := by
  obtain ⟨he,w,hw,rfl⟩ := rational_source_floor_certified_origin d s hs ε v hv
  have hc := rational_source_floor_approximation_output_class d s u hs hR ε w hw
  have hrows := (rational_source_floor_approximation_rows d s hs ε he w hw).2
  push_cast at hrows
  have hn : (floorIntervalGameClass d s u).Nonempty := ⟨_,hc⟩
  obtain ⟨w',hw',hlo,hhi⟩ := rational_source_floor_approximation_global d s u hs hu hR hn ε he
  have hsame : w'=w := Option.some.inj (hw'.symm.trans hw)
  subst w'
  refine ⟨hc,?_,?_,?_,?_⟩
  · intro a
    change _ ≤ ((w.2.bracket.2+ε/((3 : ℕ) : ℚ) : ℚ) : ℝ)
    push_cast
    exact hrows a
  · change ((w.2.bracket.2+ε/((3 : ℕ) : ℚ)-ε : ℚ) : ℝ) < _
    push_cast
    linarith
  · change _ ≤ ((w.2.bracket.2+ε/((3 : ℕ) : ℚ) : ℚ) : ℝ)
    push_cast
    exact hlo
  · change w.2.bracket.2+ε/((3 : ℕ) : ℚ)-(w.2.bracket.2+ε/((3 : ℕ) : ℚ)-ε)=ε
    ring

end SparseCompletion
