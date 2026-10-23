/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual executable certificate payload and automatic accuracy bound. -/
module
public import ProtectedSources.RationalAlgorithmCertificate
@[expose] public section
namespace SparseCompletion

def rationalCertifiedApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) : Option ((ℚ × ℚ) × RationalCertificate k m) :=
  (rationalGapAccurateApproximation d ζ).map
    (fun w => (w.1,fullRationalCertificate d.p w.2.1 w.2.2))

theorem rational_certified_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) :
    ∃ z c, rationalCertifiedApproximation d ζ=some (z,c) := by
  obtain ⟨z,q,B,h⟩ := rational_gap_accurate_complete d ζ
  exact ⟨z,fullRationalCertificate d.p q B,by
    simp only [rationalCertifiedApproximation,h,Option.map_some]⟩

theorem rational_certified_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) (z : ℚ × ℚ) (c : RationalCertificate k m)
    (h : rationalCertifiedApproximation d ζ=some (z,c)) :
    ∃ q B, rationalGapAccurateApproximation d ζ=some (z,(q,B)) ∧
      c=fullRationalCertificate d.p q B := by
  cases ha : rationalGapAccurateApproximation d ζ with
  | none => simp only [rationalCertifiedApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalCertifiedApproximation,ha,Option.map_some] using h)
    obtain ⟨hz,hc⟩ := Prod.mk.inj he
    exact ⟨w.2.1,w.2.2,by simp only [←hz],hc.symm⟩

theorem rational_certified_approximation_sound {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (c : RationalCertificate k m)
    (h : rationalCertifiedApproximation d ζ=some (z,c)) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    checkRationalGapOutput d (z.2+d.η) c=true ∧
      (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨q,B,hout,rfl⟩ := rational_certified_approximation_output d ζ z c h
  have ha := (rational_gap_approximation_output d (rationalLogRounds d.M ζ) z q B hout).2
  exact ⟨rational_gap_algorithm_checked_output d z.2 q B ha,
    rational_gap_accurate_value_enclosure d ζ hζ z q B hout⟩

end SparseCompletion
