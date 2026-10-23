/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalCountedTableCertificate
public import ProtectedSources.RationalCertificateSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_counted_certificate_check_iff {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableCertificate c K D M σ).1=true ↔
      (rationalTableAsCertificate c).check (fun h h' => (K.get h).get h')
        (fun i h => (D.get i).get h) M σ=true := by
  rw [rational_counted_table_certificate_value,RationalCertificate.check_iff,
    rational_table_conditions_iff]

theorem rational_counted_certificate_full_game {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (hc : (rationalCountedTableCertificate c K D M σ).1=true) :
    let cert := rationalTableAsCertificate c
    (∀ a,0 ≤ blockWeights (fun h => (cert.anchors h : ℝ)) cert.realQ a) ∧
    (∑ a,blockWeights (fun h => (cert.anchors h : ℝ)) cert.realQ a)=1 ∧
    IsSkew (blockMatrix (fun h h' => ((K.get h).get h' : ℝ))
      (fun i h => ((D.get i).get h : ℝ)) (cert.realB M)) ∧
    (∀ a b,-(M : ℝ) ≤ blockMatrix (fun h h' => ((K.get h).get h' : ℝ))
      (fun i h => ((D.get i).get h : ℝ)) (cert.realB M) a b ∧
      blockMatrix (fun h h' => ((K.get h).get h' : ℝ))
        (fun i h => ((D.get i).get h : ℝ)) (cert.realB M) a b ≤ (M : ℝ)) ∧
    (∀ a,response (blockMatrix (fun h h' => ((K.get h).get h' : ℝ))
      (fun i h => ((D.get i).get h : ℝ)) (cert.realB M))
      (blockWeights (fun h => (cert.anchors h : ℝ)) cert.realQ) a ≤ (σ : ℝ)) := by
  exact RationalCertificate.accepted_full_game (rationalTableAsCertificate c)
    (fun h h' => (K.get h).get h') (fun i h => (D.get i).get h) M σ
    ((rational_counted_certificate_check_iff c K D M σ).mp hc)

end SparseCompletion
