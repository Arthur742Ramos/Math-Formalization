/- AI-assisted original-paper output encoding composition; Apache-2.0.
Exact check status is external. Value encoding only; no runtime claim.
-/
module
public import RationalGaussianGraphOutputHeight
public import RationalGaussianPaperEncoding
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Input exponent for the literal general public pair's materialized table.
The canonical grid count remains explicit in the already proved weight budget. -/
def gaussianPaperGeneralTableHeight (k d m B : ℕ) (M r η : ℚ) : ℕ :=
  rationalDemandGraphOutputHeight m
    ((B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η) B+3)
      +rationalScoreInputHeight k B+B+(4*B+1))

/-- Input exponent for the literal exact public pair's materialized table. -/
def gaussianPaperExactTableHeight (k d m B : ℕ) (M r η : ℚ) : ℕ :=
  rationalDemandGraphOutputHeight m
    ((B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η-1) B+3)
      +rationalScoreInputHeight k B+B+B)

/-- Original data bounds earn the height of the actual second projection.
The first projection's size and nonnegativity are derived from the executed
compressor. No output flow, common denominator or returned-weight premise is
accepted, and no original feasible game witness is needed for a value bound. -/
theorem rational_gaussian_paper_general_flow_table_input_height {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r) (hMn : 0 ≤ M) :
    ∀ i j, RationalInputHeight
      (rationalFlowTableEntry (rationalGaussianPaperGeneralFlow D E p q M r ρ η).2 i j)
      (gaussianPaperGeneralTableHeight k d m B M r η) := by
  have hweights : ∀ i, RationalInputHeight
      ((rationalGaussianPaperGeneralFlow D E p q M r ρ η).1.get i)
      (B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η) B+3) := by
    intro i
    exact rational_input_height_of_canonical_budget
      (rational_gaussian_paper_general_flow_weight_encoding D E p q M r ρ η
        hD hE hp hqd hM hr hρ hη hq hm i)
  have hn : ∀ i, 0 ≤ (rationalGaussianPaperGeneralFlow D E p q M r ρ η).1.get i := by
    have hh := (rational_gaussian_paper_compress_contract D E q
      (fun i => rationalScore D p i-ρ) M r η (rationalCanonicalGridSize M r η) hq).1
    simpa only [rationalGaussianPaperGeneralFlow, rationalGaussianPaperGeneralVector,
      rationalGaussianPaperWeights] using hh
  have hepsilon : RationalInputHeight (ρ+η) (4*B+1) := by
    convert rational_input_height_add hρ hη using 1; omega
  exact rational_demand_graph_completion_table_separate_input_height
    (rationalGaussianPaperGeneralFlow D E p q M r ρ η).1.get (rationalScore D p) M (ρ+η)
    hweights (rational_score_input_height D p hD hp) hM hepsilon hn hMn

/-- Canonical value budget for the same literal general public pair table. -/
theorem rational_gaussian_paper_general_flow_table_canonical_bits {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hρ : RationalInputHeight ρ B) (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r) (hMn : 0 ≤ M) :
    ∀ i j, rationalCanonicalEncodingBits
      (rationalFlowTableEntry (rationalGaussianPaperGeneralFlow D E p q M r ρ η).2 i j) ≤
      2*gaussianPaperGeneralTableHeight k d m B M r η+3 := by
  intro i j
  exact rational_input_height_bits
    (rational_gaussian_paper_general_flow_table_input_height D E p q M r ρ η
      hD hE hp hqd hM hr hρ hη hq hm hMn i j)

/-- Exact-target analogue, including natural grid subtraction and zero weights.
Only original input encoding/nonnegativity/mass assumptions occur. -/
theorem rational_gaussian_paper_exact_flow_table_input_height {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r) (hMn : 0 ≤ M) :
    ∀ i j, RationalInputHeight
      (rationalFlowTableEntry (rationalGaussianPaperExactFlow D E p q M r η).2 i j)
      (gaussianPaperExactTableHeight k d m B M r η) := by
  have hweights : ∀ i, RationalInputHeight
      ((rationalGaussianPaperExactFlow D E p q M r η).1.get i)
      (B+2*gaussianPaperWeightExponent k d m (rationalCanonicalGridSize M r η-1) B+3) := by
    intro i
    exact rational_input_height_of_canonical_budget
      (rational_gaussian_paper_exact_flow_weight_encoding D E p q M r η
        hD hE hp hqd hM hr hη hq hm i)
  have hn : ∀ i, 0 ≤ (rationalGaussianPaperExactFlow D E p q M r η).1.get i := by
    have hh := (rational_gaussian_paper_compress_contract D E q
      (rationalScore D p) M r η (rationalCanonicalGridSize M r η-1) hq).1
    simpa only [rationalGaussianPaperExactFlow, rationalGaussianPaperExactVector,
      rationalGaussianPaperWeights] using hh
  exact rational_demand_graph_completion_table_separate_input_height
    (rationalGaussianPaperExactFlow D E p q M r η).1.get (rationalScore D p) M η
    hweights (rational_score_input_height D p hD hp) hM hη hn hMn

/-- Canonical value budget for the same literal exact public pair table. -/
theorem rational_gaussian_paper_exact_flow_table_canonical_bits {k d m B : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r η : ℚ)
    (hD : ∀ i a, RationalInputHeight (D i a) B)
    (hE : ∀ a i, RationalInputHeight (E a i) B)
    (hp : ∀ a, RationalInputHeight (p a) B)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 B)
    (hM : RationalInputHeight M B) (hr : RationalInputHeight r B)
    (hη : RationalInputHeight η B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r) (hMn : 0 ≤ M) :
    ∀ i j, rationalCanonicalEncodingBits
      (rationalFlowTableEntry (rationalGaussianPaperExactFlow D E p q M r η).2 i j) ≤
      2*gaussianPaperExactTableHeight k d m B M r η+3 := by
  intro i j
  exact rational_input_height_bits
    (rational_gaussian_paper_exact_flow_table_input_height D E p q M r η
      hD hE hp hqd hM hr hη hq hm hMn i j)

end SparseCompletion
