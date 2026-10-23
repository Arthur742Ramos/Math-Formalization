/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalValueCertificate
public import ProtectedSources.RationalLogRounds
@[expose] public section
namespace SparseCompletion

def rationalIntervalAccurateApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :=
  rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R (rationalLogRounds d.M ζ)

theorem rational_interval_accurate_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :
    ∃ z x B, rationalIntervalAccurateApproximation d ζ=some (z,(x,B)) :=
  rational_interval_model_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_interval_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ) (hout : rationalIntervalAccurateApproximation d ζ=some (z,(x,B))) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_interval_approximation_value_enclosure d (rationalLogRounds d.M ζ) z x B hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion
