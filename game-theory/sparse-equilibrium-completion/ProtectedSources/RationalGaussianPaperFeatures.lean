/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft. Actual Gaussian compressor at the frozen paper matrix.
The public output vector materializes all original-label weights. -/
module
public import ProtectedSources.RationalGaussianCompress
public import ProtectedSources.RationalPaperFeatures
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGaussianPaperCompress {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) : Gaussian.QVec m :=
  rationalGaussianCompressVector (rationalPaperFeatures D E v M r η L) q

/-- Coordinate projection of the vector-valued public output, for direct reuse
of the finite-grid analysis. This adds no FM call to the executed program. -/
def rationalGaussianPaperWeights {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) : Fin m → ℚ :=
  (rationalGaussianPaperCompress D E q v M r η L).get

theorem rational_gaussian_paper_compress_contract {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) (hq : ∀ i, 0 ≤ q i) :
    let q' := rationalGaussianPaperWeights D E q v M r η L
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=∑ i, q i ∧ (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ min (rationalWeightSupport q).card (k+d+L+1) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i)=∑ i, q i*E a i) ∧
      ∀ l : Fin L,
        rationalCall q' v (M*r-rationalGridNode M r η (l.val+1)) =
          rationalCall q v (M*r-rationalGridNode M r η (l.val+1)) := by
  obtain ⟨hp, _, hc⟩ := rational_gaussian_compress_vector_contract
    (rationalPaperFeatures D E v M r η L) q hq 0 (fun _ => rfl)
  refine ⟨hp.1, hp.2.1, hp.2.2.2, ?_, ?_, ?_, ?_⟩
  · simpa only [rationalGaussianPaperWeights, rationalGaussianPaperCompress, Nat.add_assoc] using hc
  · intro a
    simpa [rationalGaussianPaperWeights, rationalGaussianPaperCompress, rationalPaperFeatures] using
      hp.2.2.1 (Fin.castAdd (d+L) a).succ
  · intro a
    simpa [rationalGaussianPaperWeights, rationalGaussianPaperCompress, rationalPaperFeatures] using
      hp.2.2.1 (Fin.natAdd k (Fin.castAdd L a)).succ
  · intro l
    simpa [rationalGaussianPaperWeights, rationalGaussianPaperCompress, rationalPaperFeatures, rationalCall] using
      hp.2.2.1 (Fin.natAdd k (Fin.natAdd d l)).succ

end SparseCompletion
