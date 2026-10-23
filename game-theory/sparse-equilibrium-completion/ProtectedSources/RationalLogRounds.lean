/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Logarithmic bisection rounds; no polynomial LP or bit-cost assertion. -/
module
public import ProtectedSources.RationalGapValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalLogRounds (M ζ : ℚ) : ℕ := Nat.log2 (Nat.ceil (M/ζ))+1

theorem rational_log_rounds_width (M ζ : ℚ) (hζ : 0 < ζ) :
    M/((2 : ℕ) : ℚ)^rationalLogRounds M ζ < ζ := by
  have hc : M/ζ ≤ (Nat.ceil (M/ζ) : ℚ) := Nat.le_ceil (M/ζ)
  have hn : (Nat.ceil (M/ζ) : ℚ) < ((2 : ℕ) : ℚ)^rationalLogRounds M ζ := by
    unfold rationalLogRounds
    exact_mod_cast Nat.lt_log2_self (n := Nat.ceil (M/ζ))
  have hp : (0 : ℚ) < ((2 : ℕ) : ℚ)^rationalLogRounds M ζ := pow_pos (by norm_num) _
  have hm := (div_lt_iff₀ hζ).mp (lt_of_le_of_lt hc hn)
  exact (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using hm)

def rationalGapAccurateApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalGapModel k m I) (ζ : ℚ) :
    Option ((ℚ × ℚ) × ((Fin m → ℚ) × (Fin m → Fin m → ℚ))) :=
  rationalGapApproximation d (rationalLogRounds d.M ζ)

theorem rational_gap_accurate_complete {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) :
    ∃ z q B, rationalGapAccurateApproximation d ζ=some (z,(q,B)) :=
  rational_gap_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_gap_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalGapModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalGapAccurateApproximation d ζ=some (z,(q,B))) :
    let V := fixedGameValue (fun a b => (d.K a b : ℝ)) (fun i a => (d.D i a : ℝ))
      (fun a => (d.p a : ℝ)) d.M (rationalRealRepertoire d.R d.r)
    (z.1 : ℝ) ≤ V ∧ V ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_gap_approximation_value_enclosure d (rationalLogRounds d.M ζ) z q B hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion
