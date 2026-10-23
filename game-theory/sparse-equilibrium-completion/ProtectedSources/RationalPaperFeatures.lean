/- AI-assisted formalization under the repository Apache-2.0 license.
Separate development draft. Actual FM compressor; no polynomial bound. -/
module
public import ProtectedSources.RationalFeatureIterate
public import ProtectedSources.RationalCanonicalGrid
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Mass occurs exactly once, followed by k anchors, d extra moments and L
hinges. L=H is general; L=H-1 is the exact-equilibrium specialization. -/
def rationalPaperFeatures {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) :
    Fin (k+(d+L)+1) → Fin m → ℚ :=
  Fin.cons (α := fun _ => Fin m → ℚ) (fun _ => 1)
    (Fin.append (fun a i => D i a)
      (Fin.append E (fun l i => max (v i-(M*r-rationalGridNode M r η (l.val+1))) 0)))

def rationalPaperCompress {k d m : ℕ} (D : Fin m → Fin k → ℚ)
    (E : Fin d → Fin m → ℚ) (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) :
    Fin m → ℚ := rationalFeatureCompress (rationalPaperFeatures D E v M r η L) q

/-- All retained features and original zeros belong to the exact executed
output. The support bound includes the single normalization coordinate. -/
theorem rational_paper_compress_contract {k d m : ℕ}
    (D : Fin m → Fin k → ℚ) (E : Fin d → Fin m → ℚ)
    (q v : Fin m → ℚ) (M r η : ℚ) (L : ℕ) (hq : ∀ i, 0 ≤ q i) :
    let q' := rationalPaperCompress D E q v M r η L
    (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i) = ∑ i, q i ∧
      (∀ i, q i=0 → q' i=0) ∧
      (rationalWeightSupport q').card ≤ min (rationalWeightSupport q).card (k+d+L+1) ∧
      (∀ a, (∑ i, q' i*D i a) = ∑ i, q i*D i a) ∧
      (∀ a, (∑ i, q' i*E a i) = ∑ i, q i*E a i) ∧
      ∀ l : Fin L,
        rationalCall q' v (M*r-rationalGridNode M r η (l.val+1)) =
          rationalCall q v (M*r-rationalGridNode M r η (l.val+1)) := by
  obtain ⟨hp, _, hc⟩ := rational_feature_compress_contract
    (rationalPaperFeatures D E v M r η L) q hq 0 (fun _ => rfl)
  refine ⟨hp.1, hp.2.1, hp.2.2.2, (by simpa only [rationalPaperCompress, Nat.add_assoc] using hc), ?_, ?_, ?_⟩
  · intro a
    simpa [rationalPaperCompress, rationalPaperFeatures] using hp.2.2.1 (Fin.castAdd (d+L) a).succ
  · intro a
    simpa [rationalPaperCompress, rationalPaperFeatures] using
      hp.2.2.1 (Fin.natAdd k (Fin.castAdd L a)).succ
  · intro l
    simpa [rationalPaperCompress, rationalPaperFeatures, rationalCall] using
      hp.2.2.1 (Fin.natAdd k (Fin.natAdd d l)).succ

end SparseCompletion
