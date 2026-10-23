/- AI-assisted formalization under repository Apache-2.0.
Input-derived canonical component bounds for the actual rational score,
grid nodes, envelope and both executed grid-size definitions. -/
module
public import RationalInputHeight
public import RationalCanonicalGrid
public import RationalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalScoreInputHeight (k B : ℕ) : ℕ := k+4*B*(k+1)
def rationalGridNodeInputHeight (B J : ℕ) : ℕ := 8+6*B+8*J
def rationalGridThresholdInputHeight (B J : ℕ) : ℕ :=
  2*(4*B+rationalGridNodeInputHeight B J)+1
def rationalEnvelopeInputHeight (B J : ℕ) : ℕ :=
  8*rationalGridNodeInputHeight B J+12+4*B

theorem rational_score_input_height {k m B : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B) (i : Fin m) :
    RationalInputHeight (rationalScore D p i) (rationalScoreInputHeight k B) := by
  have hterm : ∀ a, RationalInputHeight (D i a*p a) (4*B) := by
    intro a
    convert rational_input_height_mul (hD i a) (hp a) using 1; omega
  simpa only [rationalScore, rationalScoreInputHeight] using
    rational_input_height_fin_sum (fun a => D i a*p a) hterm

theorem rational_grid_node_input_height (M r η : ℚ) (B J l : ℕ)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) (hl : l ≤ (Nat.pow 2 J)) :
    RationalInputHeight (rationalGridNode M r η l) (rationalGridNodeInputHeight B J) := by
  have htwo : RationalInputHeight (2 : ℚ) 2 := rational_input_height_nat 2 2 (by norm_num)
  have hli := rational_input_height_nat l J hl
  have hleft := rational_input_height_mul (rational_input_height_mul htwo hη)
    (rational_input_height_mul hli hli)
  have hright := rational_input_height_mul (rational_input_height_mul htwo hM) hr
  unfold rationalGridNode
  rw [pow_two]
  apply rational_input_height_min
  · exact rational_input_height_mono hleft (by unfold rationalGridNodeInputHeight; omega)
  · exact rational_input_height_mono hright (by unfold rationalGridNodeInputHeight; omega)

theorem rational_grid_threshold_input_height (M r η : ℚ) (B J l : ℕ)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) (hl : l ≤ (Nat.pow 2 J)) :
    RationalInputHeight (M*r-rationalGridNode M r η l)
      (rationalGridThresholdInputHeight B J) := by
  have hprod : RationalInputHeight (M*r) (4*B) := by
    convert rational_input_height_mul hM hr using 1; omega
  exact rational_input_height_sub hprod (rational_grid_node_input_height M r η B J l hM hr hη hl)

theorem rational_envelope_grid_input_height (M r η : ℚ) (B J l : ℕ)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) (hl : l ≤ (Nat.pow 2 J)) :
    RationalInputHeight (rationalEnvelope M r (M*r-rationalGridNode M r η l))
      (rationalEnvelopeInputHeight B J) := by
  have hnode := rational_grid_node_input_height M r η B J l hM hr hη hl
  have hfour : RationalInputHeight (4 : ℚ) 3 := rational_input_height_nat 4 3 (by norm_num)
  have hvalue : rationalEnvelope M r (M*r-rationalGridNode M r η l) =
      (rationalGridNode M r η l)^2/(4*M) := by
    unfold rationalEnvelope
    congr 1
    ring
  rw [hvalue, pow_two]
  have hh := rational_input_height_div (rational_input_height_mul hnode hnode)
    (rational_input_height_mul hfour hM)
  convert hh using 1; unfold rationalEnvelopeInputHeight; omega

theorem rational_grid_ratio_input_height (M r η : ℚ) (B : ℕ)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) : RationalInputHeight (M*r/η) (10*B) := by
  convert rational_input_height_div (rational_input_height_mul hM hr) hη using 1; omega

/-- Neither positivity nor a guessed bound on an output grid index is needed:
the exact executed integer endpoint is bounded from the canonical input data. -/
theorem rational_grid_sizes_input_bound (M r η : ℚ) (B : ℕ)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) :
    rationalGridSize M r η ≤ (Nat.pow 2 (10*B+1)) ∧
      rationalCanonicalGridSize M r η ≤ (Nat.pow 2 (10*B+1)) := by
  have hm := rational_input_height_magnitude (rational_grid_ratio_input_height M r η B hM hr hη)
  have hc : Nat.ceil (M*r/η) ≤ (Nat.pow 2 (10*B)) :=
    Nat.ceil_le.mpr ((le_abs_self _).trans hm)
  have hs := (Nat.sqrt_le_self (Nat.ceil (M*r/η))).trans hc
  have hp : 0 < Nat.pow 2 (10*B) := Nat.two_pow_pos (10*B)
  have hpstep : Nat.pow 2 (10*B+1) = Nat.pow 2 (10*B)*2 := rfl
  constructor
  · unfold rationalGridSize
    rw [hpstep]
    omega
  · dsimp only [rationalCanonicalGridSize, rationalCeilSqrt]
    split <;> rw [hpstep] <;> omega

theorem rational_grid_row_endpoint_input_bound {M r η : ℚ} {B : ℕ}
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) (l : Fin (rationalGridSize M r η)) :
    l.val+1 ≤ (Nat.pow 2 (10*B+1)) :=
  (Nat.succ_le_of_lt l.isLt).trans (rational_grid_sizes_input_bound M r η B hM hr hη).1

theorem rational_canonical_row_endpoint_input_bound {M r η : ℚ} {B L : ℕ}
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) (hL : L ≤ rationalCanonicalGridSize M r η) (l : Fin L) :
    l.val+1 ≤ (Nat.pow 2 (10*B+1)) :=
  ((Nat.succ_le_of_lt l.isLt).trans hL).trans
    (rational_grid_sizes_input_bound M r η B hM hr hη).2

end SparseCompletion
