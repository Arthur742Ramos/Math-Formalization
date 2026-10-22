/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Executable exact rational elimination, with no polynomial bit-cost assertion. -/
module
public import RationalGapAlgorithm
public import RationalRepertoire
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalGapModel (k m : ℕ) (I : Type*) where
  K : Fin k → Fin k → ℚ
  D : Fin m → Fin k → ℚ
  p : Fin k → ℚ
  M : ℚ
  r : ℚ
  η : ℚ
  R : RationalLinearSystem I m
  positiveBound : 0 < M
  positiveSlack : 0 < η
  anchorNonneg : ∀ a, 0 ≤ p a
  normalized : (∑ a, p a)+r=1
  anchorSkew : ∀ a b, K a b= -K b a
  anchorBounds : ∀ a b, -M ≤ K a b ∧ K a b ≤ M
  crossBounds : ∀ i a, -M ≤ D i a ∧ D i a ≤ M
  repertoireNonempty : (rationalRealRepertoire R r).Nonempty

theorem rational_gap_model_value_bounds {k m : ℕ} {I : Type*}
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    0 ≤ V ∧ V ≤ (d.M : ℝ) ∧
      fixedAnchorFeasible (rationalRealRepertoire d.R d.r)
        (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
        (fun a => (d.p a : ℝ)) d.M d.r V := by
  apply fixed_game_value_bounds _ _ _ _ _ _ (by exact_mod_cast le_of_lt d.positiveBound)
    (rational_real_repertoire_compact d.R d.r) d.repertoireNonempty
    (fun a => by exact_mod_cast d.anchorNonneg a) (by exact_mod_cast d.normalized)
    (fun _ h => h.2)
  · intro a b
    change (d.K a b : ℝ)= -(d.K b a : ℝ)
    exact_mod_cast d.anchorSkew a b
  · intro a b
    exact_mod_cast d.anchorBounds a b
  · intro i a
    exact_mod_cast d.crossBounds i a

theorem rational_gap_model_upper_feasible {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) :
    RationalGapExists d.K d.D d.p d.M d.r d.M d.η d.R := by
  obtain ⟨hV0,hVM,x,hx,hx0,hxm,B,hB,hb,hrows⟩ := rational_gap_model_value_bounds d
  obtain ⟨q,hq⟩ := exact_game_rational_gap_solve d.K d.D d.p x B d.M d.r d.M d.η d.R hx.1
    d.positiveBound hx0 hxm hB hb (fun a => le_trans (hrows a) hVM)
  have hs := rational_gap_solve_sound d.K d.D d.p d.M d.r d.M d.η d.R q hq
  exact ⟨q,(rational_gap_check_iff _ _ _ _ _ _ _ _).mp hs.1,hs.2⟩

def rationalGapApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (n : ℕ) :
    Option ((ℚ × ℚ) × ((Fin m → ℚ) × (Fin m → Fin m → ℚ))) :=
  let z := rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n
  (rationalGapAlgorithm d.K d.D d.p d.M d.r z.2 d.η d.R).map (fun w => (z,w))

theorem rational_gap_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (n : ℕ) :
    ∃ z q B, rationalGapApproximation d n=some (z,(q,B)) := by
  have hz := rational_gap_search_bracket d.K d.D d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_gap_model_upper_feasible d)
  obtain ⟨q,B,h⟩ := rational_gap_algorithm_complete d.K d.D d.p d.M d.r
    (rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n).2 d.η d.R
    d.positiveBound d.positiveSlack hz.2.2.2.1
  exact ⟨rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n,q,B,by
    simp only [rationalGapApproximation,h,Option.map_some]⟩

theorem rational_gap_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapApproximation d n=some (z,(q,B))) :
    z=rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n ∧
    rationalGapAlgorithm d.K d.D d.p d.M d.r z.2 d.η d.R=some (q,B) := by
  cases ha : rationalGapAlgorithm d.K d.D d.p d.M d.r
    (rationalGapSearch d.K d.D d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalGapApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalGapApproximation,ha,Option.map_some] using h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_gap_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalGapApproximation d n=some (z,(q,B))) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  obtain ⟨hz,ha⟩ := rational_gap_approximation_output d n z q B hout
  have hbr := rational_gap_search_bracket d.K d.D d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_gap_model_upper_feasible d)
  rw [←hz] at hbr
  have hs := rational_gap_algorithm_sound d.K d.D d.p d.M d.r z.2 d.η d.R q B ha
  have hcheck := (rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hs.2.1
  have hB : reconstructRationalGap d.D d.p q d.M z.2 d.η=some B := by
    unfold rationalGapAlgorithm at ha
    cases hq : rationalGapSolve d.K d.D d.p d.M d.r z.2 d.η d.R with
    | none => simp only [hq,Option.bind_none] at ha; cases ha
    | some y =>
      cases hb : rationalResidualCompletion y (rationalScore d.D d.p) d.M (z.2+d.η) with
      | none => simp only [hq,Option.bind_some,hb,Option.map_none] at ha; cases ha
      | some C =>
        have he : (y,C)=(q,B) := Option.some.inj (by simpa only [hq,Option.bind_some,hb,Option.map_some] using ha)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        exact hb
  have hn := rational_gap_reconstruction_normalized_full_game d.K d.D d.p q d.M d.r z.2 d.η
    d.positiveSlack d.anchorNonneg d.normalized d.anchorSkew d.anchorBounds d.crossBounds hcheck B hB
  have hbR := rational_residual_completion_real_sound q (rationalScore d.D d.p) d.M (z.2+d.η) B hB
  have hqR : (fun i => (q i : ℝ)) ∈ rationalRealRepertoire d.R d.r := by
    refine ⟨(rational_linear_real_cast_iff d.R q).mpr hs.1,?_,?_⟩
    · intro i
      change (0 : ℝ) ≤ (q i : ℝ)
      exact_mod_cast hs.2.1.1 i
    · change (∑ i, (q i : ℝ))=(d.r : ℝ)
      exact_mod_cast hs.2.1.2.1
  have hu := le_trans (fixed_game_value_le_witness _ _ _ _ _
    (rational_real_repertoire_compact d.R d.r) _ _ ⟨hbR.1,hbR.2.1⟩ hqR)
    ((exploitability_le_iff _ _ _).mpr hn.2.2.2.2)
  refine ⟨?_,hu,hbr.2.2.2.2.2⟩
  obtain ⟨hV0,_,x,hx,hx0,hxm,C,hC,hcb,hrows⟩ := rational_gap_model_value_bounds d
  rcases hbr.2.2.2.2.1 with hzero | hno
  · rw [hzero,Rat.cast_zero]; exact hV0
  · by_contra hlow
    have hvL := le_of_lt (lt_of_not_ge hlow)
    obtain ⟨y,hy⟩ := exact_game_rational_gap_solve d.K d.D d.p x C d.M d.r z.1 d.η d.R hx.1
      d.positiveBound hx0 hxm hC hcb (fun a => le_trans (hrows a) hvL)
    have hh := rational_gap_solve_sound d.K d.D d.p d.M d.r z.1 d.η d.R y hy
    exact hno ⟨y,(rational_gap_check_iff _ _ _ _ _ _ _ _).mp hh.1,hh.2⟩

end SparseCompletion
