/- AI-assisted formalization under repository Apache-2.0.
Polynomial value-encoding bounds for every row of the actual fixed-anchor
rational LP constructor, including generated hinge endpoints and envelopes.
No claim about FM output size, arithmetic cost or solver runtime. -/
module
public import RationalGridInputHeight
public import RationalGapDecision
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFixedAnchorInputHeight (k B : ℕ) : ℕ := 1024*(k+1)*(B+1)

theorem rational_gap_coefficient_input_height {k m B : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (row : RationalGapRow k m (rationalGridSize M r η)) (i : Fin m) :
    RationalInputHeight (rationalGapCoefficient D p M r ρ η row i)
      (rationalFixedAnchorInputHeight k B) := by
  have hbase : B ≤ rationalFixedAnchorInputHeight k B := by
    unfold rationalFixedAnchorInputHeight
    nlinarith [Nat.zero_le (k*B)]
  have hz := rational_input_height_zero (rationalFixedAnchorInputHeight k B)
  have ho := rational_input_height_one (rationalFixedAnchorInputHeight k B)
  have hn := rational_input_height_neg ho
  have hhinge (l : Fin (rationalGridSize M r η)) :
      RationalInputHeight
        (max (rationalScore D p i-ρ-(M*r-rationalGridNode M r η (l.val+1))) 0)
        (rationalFixedAnchorInputHeight k B) := by
    have hs := rational_score_input_height D p hD hp i
    have ht := rational_grid_threshold_input_height M r η B (10*B+1) (l.val+1)
      hM hr hη (rational_grid_row_endpoint_input_bound hM hr hη l)
    apply rational_input_height_max _ hz
    apply rational_input_height_mono (rational_input_height_sub (rational_input_height_sub hs hρ) ht)
    unfold rationalScoreInputHeight rationalGridThresholdInputHeight
      rationalGridNodeInputHeight rationalFixedAnchorInputHeight
    nlinarith [Nat.zero_le (k*B)]
  rcases row with j | row
  · simp only [rationalGapCoefficient, Sum.elim_inl]
    split
    · exact hn
    · exact hz
  · rcases row with s | row
    · simp only [rationalGapCoefficient, Sum.elim_inr, Sum.elim_inl]
      split
      · exact ho
      · exact hn
    · rcases row with j | row
      · exact hz
      · rcases row with a | l
        · exact rational_input_height_mono (rational_input_height_neg (hD i a)) hbase
        · exact hhinge l

theorem rational_gap_right_side_input_height {k m B : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (row : RationalGapRow k m (rationalGridSize M r η)) :
    RationalInputHeight (rationalGapRightSide K D p M r ρ η row)
      (rationalFixedAnchorInputHeight k B) := by
  have hbase : B ≤ rationalFixedAnchorInputHeight k B := by
    unfold rationalFixedAnchorInputHeight
    nlinarith [Nat.zero_le (k*B)]
  have hz := rational_input_height_zero (rationalFixedAnchorInputHeight k B)
  rcases row with j | row
  · exact hz
  · rcases row with s | row
    · simp only [rationalGapRightSide, Sum.elim_inr, Sum.elim_inl]
      split
      · exact rational_input_height_mono hr hbase
      · exact rational_input_height_mono (rational_input_height_neg hr) hbase
    · rcases row with i | row
      · have hs := rational_score_input_height D p hD hp i
        apply rational_input_height_mono
          (rational_input_height_sub (rational_input_height_add hρ (rational_input_height_mul hM hr)) hs)
        unfold rationalScoreInputHeight rationalFixedAnchorInputHeight
        nlinarith [Nat.zero_le (k*B)]
      · rcases row with a | l
        · have hs : RationalInputHeight (∑ b, K a b*p b) (rationalScoreInputHeight k B) := by
            apply rational_input_height_fin_sum
            intro b
            convert rational_input_height_mul (hK a b) (hp b) using 1; omega
          apply rational_input_height_mono (rational_input_height_sub hρ hs)
          unfold rationalScoreInputHeight rationalFixedAnchorInputHeight
          nlinarith [Nat.zero_le (k*B)]
        · apply rational_input_height_mono
            (rational_envelope_grid_input_height M r η B (10*B+1) (l.val+1)
              hM hr hη (rational_grid_row_endpoint_input_bound hM hr hη l))
          unfold rationalEnvelopeInputHeight rationalGridNodeInputHeight rationalFixedAnchorInputHeight
          nlinarith [Nat.zero_le (k*B)]

/-- Every entry belongs to the literal LP passed to `rationalLPSolve` by the
fixed-anchor constructor. Only input canonical num/den bounds are premises. -/
theorem rational_gap_system_input_height {k m B : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B) :
    (∀ row i, RationalInputHeight ((rationalGapSystem K D p M r ρ η).coefficient row i)
      (rationalFixedAnchorInputHeight k B)) ∧
      ∀ row, RationalInputHeight ((rationalGapSystem K D p M r ρ η).rightSide row)
        (rationalFixedAnchorInputHeight k B) :=
  ⟨rational_gap_coefficient_input_height D p M r ρ η hD hp hM hr hρ hη,
    rational_gap_right_side_input_height K D p M r ρ η hK hD hp hM hr hρ hη⟩

def rationalLinearSystemEncodingBits {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) : ℕ :=
  ∑ row, ((∑ i, rationalCanonicalEncodingBits (S.coefficient row i))+
    rationalCanonicalEncodingBits (S.rightSide row))

theorem rational_linear_system_encoding_bits_of_entry_bound {I : Type*} [Fintype I]
    {n H : ℕ} (S : RationalLinearSystem I n)
    (hc : ∀ row i, RationalInputHeight (S.coefficient row i) H)
    (hr : ∀ row, RationalInputHeight (S.rightSide row) H) :
    rationalLinearSystemEncodingBits S ≤ Fintype.card I*(n+1)*(2*H+3) := by
  unfold rationalLinearSystemEncodingBits
  calc
    _ ≤ ∑ row : I, (n+1)*(2*H+3) := by
      apply Finset.sum_le_sum
      intro row _
      have hsum : (∑ i, rationalCanonicalEncodingBits (S.coefficient row i)) ≤ n*(2*H+3) := by
        calc
          _ ≤ ∑ _ : Fin n, (2*H+3) := Finset.sum_le_sum (fun i _ => rational_input_height_bits (hc row i))
          _ = _ := by simp
      have hright := rational_input_height_bits (hr row)
      nlinarith
    _ = _ := by simp; ring

theorem rational_gap_system_encoding_bits {k m B : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hK : ∀ a b, RationalInputHeight (K a b) B)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B) :
    rationalLinearSystemEncodingBits (rationalGapSystem K D p M r ρ η) ≤
      (2*m+2+k+rationalGridSize M r η)*(m+1)*(2048*(k+1)*(B+1)+3) := by
  obtain ⟨hc, hs⟩ := rational_gap_system_input_height K D p M r ρ η hK hD hp hM hr hρ hη
  have hh := rational_linear_system_encoding_bits_of_entry_bound (rationalGapSystem K D p M r ρ η) hc hs
  rw [rational_gap_encoding_rows] at hh
  convert hh using 1; unfold rationalFixedAnchorInputHeight; ring

end SparseCompletion
