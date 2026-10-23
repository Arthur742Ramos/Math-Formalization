/- AI-assisted formalization under repository Apache-2.0.
Input-derived encoding bounds for the literal feature-kernel LPs called by
the actual general/exact paper compressor. Current weights enter coefficients
only through support tests; no FM output-height or runtime theorem is claimed. -/
module
public import ProtectedSources.RationalGapInputHeight
public import ProtectedSources.RationalPaperFeatures
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_paper_shift_features_input_height {k d m B L : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hL : L ≤ rationalCanonicalGridSize M r η)
    (row : Fin (k+(d+L)+1)) (i : Fin m) :
    RationalInputHeight
      (rationalPaperFeatures D E (fun i => rationalScore D p i-ρ) M r η L row i)
      (rationalFixedAnchorInputHeight k B) := by
  have hbase : B ≤ rationalFixedAnchorInputHeight k B := by
    unfold rationalFixedAnchorInputHeight
    nlinarith [Nat.zero_le (k*B)]
  have hhinge (l : Fin L) : RationalInputHeight
      (max (rationalScore D p i-ρ-(M*r-rationalGridNode M r η (l.val+1))) 0)
      (rationalFixedAnchorInputHeight k B) := by
    have hs := rational_score_input_height D p hD hp i
    have ht := rational_grid_threshold_input_height M r η B (10*B+1) (l.val+1)
      hM hr hη (rational_canonical_row_endpoint_input_bound hM hr hη hL l)
    apply rational_input_height_max _ (rational_input_height_zero _)
    apply rational_input_height_mono (rational_input_height_sub (rational_input_height_sub hs hρ) ht)
    unfold rationalScoreInputHeight rationalGridThresholdInputHeight
      rationalGridNodeInputHeight rationalFixedAnchorInputHeight
    nlinarith [Nat.zero_le (k*B)]
  refine Fin.cases ?_ (fun tail => ?_) row
  · exact rational_input_height_one _
  · refine Fin.addCases (fun a => ?_) (fun tail' => ?_) tail
    · simpa [rationalPaperFeatures] using rational_input_height_mono (hD i a) hbase
    · refine Fin.addCases (fun a => ?_) (fun l => ?_) tail'
      · simpa [rationalPaperFeatures] using rational_input_height_mono (hE a i) hbase
      · simpa [rationalPaperFeatures] using hhinge l

theorem rational_feature_kernel_system_input_height {f m H : ℕ}
    (A : Fin f → Fin m → ℚ) (q : Fin m → ℚ) (pivot : Fin m)
    (hA : ∀ row i, RationalInputHeight (A row i) H) :
    (∀ row i, RationalInputHeight ((rationalFeatureKernelSystem A q pivot).coefficient row i) H) ∧
      ∀ row, RationalInputHeight ((rationalFeatureKernelSystem A q pivot).rightSide row) H := by
  have hz := rational_input_height_zero H
  have ho := rational_input_height_one H
  have hc (row : RationalFeatureEquation f m) (i : Fin m) :
      RationalInputHeight (rationalFeatureEquationCoefficient A q pivot row i) H := by
    rcases row with a | u | j | u
    · exact hA a i
    · exact ho
    · simp only [rationalFeatureEquationCoefficient, Sum.elim_inr, Sum.elim_inl]
      split
      · exact hz
      · split
        · exact ho
        · exact hz
    · simp only [rationalFeatureEquationCoefficient, Sum.elim_inr]
      split
      · exact ho
      · exact hz
  have hs (row : RationalFeatureEquation f m) :
      RationalInputHeight (rationalFeatureEquationRight row) H := by
    rcases row with a | u | j | u
    · exact hz
    · exact hz
    · exact hz
    · exact ho
  constructor
  · rintro ⟨row, b⟩ i
    cases b
    · exact rational_input_height_neg (hc row i)
    · exact hc row i
  · rintro ⟨row, b⟩
    cases b
    · exact rational_input_height_neg (hs row)
    · exact hs row

theorem rational_feature_kernel_system_encoding_bits {f m H : ℕ}
    (A : Fin f → Fin m → ℚ) (q : Fin m → ℚ) (pivot : Fin m)
    (hA : ∀ row i, RationalInputHeight (A row i) H) :
    rationalLinearSystemEncodingBits (rationalFeatureKernelSystem A q pivot) ≤
      2*(f+m+2)*(m+1)*(2*H+3) := by
  obtain ⟨hc, hs⟩ := rational_feature_kernel_system_input_height A q pivot hA
  have hh := rational_linear_system_encoding_bits_of_entry_bound (rationalFeatureKernelSystem A q pivot) hc hs
  have hcard : Fintype.card (RationalFeatureEquation f m × Bool) = 2*(f+m+2) := by
    simp only [RationalFeatureEquation, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit, Fintype.card_prod, Fintype.card_bool]
    ring
  simpa only [hcard] using hh

/-- This is the exact LP family passed to the original paper compressor's
kernel search, for every current rational weight vector and chosen pivot.
The same canonical-grid bound covers L=H and the exact L=H-1 construction. -/
theorem rational_paper_shift_kernel_input_encoding_bits {k d m B L : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ)
    (q : Fin m → ℚ) (pivot : Fin m) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hL : L ≤ rationalCanonicalGridSize M r η) :
    rationalLinearSystemEncodingBits
      (rationalFeatureKernelSystem
        (rationalPaperFeatures D E (fun i => rationalScore D p i-ρ) M r η L) q pivot) ≤
      2*(k+d+L+m+3)*(m+1)*(2048*(k+1)*(B+1)+3) := by
  have hA := rational_paper_shift_features_input_height D E p M r ρ η hD hE hp hM hr hρ hη hL
  have hh := rational_feature_kernel_system_encoding_bits
    (rationalPaperFeatures D E (fun i => rationalScore D p i-ρ) M r η L) q pivot hA
  convert hh using 1; unfold rationalFixedAnchorInputHeight; ring

theorem rational_paper_general_kernel_input_encoding_bits {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ)
    (q : Fin m → ℚ) (pivot : Fin m) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B) :
    rationalLinearSystemEncodingBits
      (rationalFeatureKernelSystem
        (rationalPaperFeatures D E (fun i => rationalScore D p i-ρ) M r η
          (rationalCanonicalGridSize M r η)) q pivot) ≤
      2*(k+d+rationalCanonicalGridSize M r η+m+3)*(m+1)*(2048*(k+1)*(B+1)+3) :=
  rational_paper_shift_kernel_input_encoding_bits D E p q pivot M r ρ η hD hE hp hM hr hρ hη le_rfl

theorem rational_paper_exact_kernel_input_encoding_bits {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ) (p : Fin k → ℚ)
    (q : Fin m → ℚ) (pivot : Fin m) (M r η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B) :
    rationalLinearSystemEncodingBits
      (rationalFeatureKernelSystem
        (rationalPaperFeatures D E (rationalScore D p) M r η
          (rationalCanonicalGridSize M r η-1)) q pivot) ≤
      2*(k+d+(rationalCanonicalGridSize M r η-1)+m+3)*(m+1)*(2048*(k+1)*(B+1)+3) := by
  simpa only [sub_zero] using rational_paper_shift_kernel_input_encoding_bits
    (L := rationalCanonicalGridSize M r η-1) D E p q pivot M r 0 η hD hE hp hM hr
      (rational_input_height_zero B) hη (Nat.sub_le _ _)

end SparseCompletion
