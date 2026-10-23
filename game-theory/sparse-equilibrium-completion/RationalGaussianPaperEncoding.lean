/- AI-assisted separate source draft; Apache-2.0.
Original paper-input bounds for the actual materialized Gaussian weights.
Exact check status is external. Value encoding only; no runtime claim.
-/
module
public import RationalGaussianCompressionEncoding
public import RationalGaussianPaperFlow
public import RationalPaperLPInputHeight
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def gaussianPaperWeightExponent (k d m L B : ℕ) : ℕ :=
  B*m+m*(gaussianCompressionDirectionExponent (k+(d+L)+1) m
    (rationalFixedAnchorInputHeight k B)*(m+1))

/-- Every original rational input is bounded before compression. The result
is the actual materialized vector, including all repeated support deletions;
no direction or returned-weight size bound is a caller premise. -/
theorem rational_gaussian_paper_shift_encoding_bits {k d m B L : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hL : L ≤ rationalCanonicalGridSize M r η) :
    ∀ i, rationalCanonicalEncodingBits
      ((rationalGaussianPaperCompress D E q (fun j => rationalScore D p j-ρ) M r η L).get i)
        ≤ B+2*gaussianPaperWeightExponent k d m L B+3 := by
  have hA := rational_paper_shift_features_input_height D E p M r ρ η
    hD hE hp hM hr hρ hη hL
  have hrb : r ≤ ((Nat.pow 2 B : ℕ) : ℚ) :=
    (le_abs_self r).trans (rational_input_height_magnitude hr)
  exact rational_gaussian_compress_encoding_bits
    (rationalPaperFeatures D E (fun j => rationalScore D p j-ρ) M r η L)
    (rationalFixedAnchorInputHeight k B)
    (fun a i => (hA a i).1) (fun a i => (hA a i).2)
    q B B r hqd hq hm hrb

theorem rational_gaussian_paper_general_flow_weight_encoding {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r) :
    ∀ i, rationalCanonicalEncodingBits
      ((rationalGaussianPaperGeneralFlow D E p q M r ρ η).1.get i)
      ≤ B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η) B+3 := by
  exact rational_gaussian_paper_shift_encoding_bits D E p q M r ρ η
    hD hE hp hqd hM hr hρ hη hq hm (Nat.le_refl _)

theorem rational_gaussian_paper_exact_flow_weight_encoding {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r) :
    ∀ i, rationalCanonicalEncodingBits
      ((rationalGaussianPaperExactFlow D E p q M r η).1.get i)
      ≤ B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η-1) B+3 := by
  have hh := rational_gaussian_paper_shift_encoding_bits D E p q M r 0 η
    hD hE hp hqd hM hr (rational_input_height_zero B) hη hq hm
    (Nat.sub_le (rationalCanonicalGridSize M r η) 1)
  simpa only [rationalGaussianPaperExactFlow, rationalGaussianPaperExactVector, sub_zero] using hh

end SparseCompletion
