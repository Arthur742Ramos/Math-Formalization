/- AI-assisted formalization under the repository Apache-2.0 license.
Check a supplied rational flow certificate and compute every residual entry,
including zero-weight rows. Rejection does not certify infeasibility: the
certificate may be wrong even when some other flow exists. No flow finder or
polynomial-time guarantee is asserted. -/
module
public import RationalFlowZeroRows
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalFlowCertificateCheck {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) : Bool :=
  decide ((0 ≤ M) ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
    (∀ i, t i ≤ ε+M*r) ∧
    RationalSaturatedFlow (fun i => q i*(t i-ε)) (fun i j => M*q i*q j) F y)

def rationalFlowCompletionFromCertificate {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) : Option (Fin m → Fin m → ℚ) :=
  if rationalFlowCertificateCheck q t M r ε F y then some (rationalFlowDecodeWithZeros q F M)
  else none

theorem rational_flow_certificate_check_iff {m : ℕ} (q t : Fin m → ℚ) (M r ε : ℚ)
    (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) :
    rationalFlowCertificateCheck q t M r ε F y = true ↔
      (0 ≤ M) ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
      (∀ i, t i ≤ ε+M*r) ∧
      RationalSaturatedFlow (fun i => q i*(t i-ε)) (fun i j => M*q i*q j) F y := by
  simp only [rationalFlowCertificateCheck,decide_eq_true_eq]

theorem rational_flow_certificate_completion_sound {m : ℕ} (q t : Fin m → ℚ)
    (M r ε : ℚ) (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ)
    (B : Fin m → Fin m → ℚ)
    (ho : rationalFlowCompletionFromCertificate q t M r ε F y = some B) :
    B = rationalFlowDecodeWithZeros q F M ∧ ResidualRatConditions q t M ε B := by
  unfold rationalFlowCompletionFromCertificate at ho
  split at ho
  · rename_i hc
    have hB := Option.some.inj ho
    subst B
    rcases (rational_flow_certificate_check_iff q t M r ε F y).mp hc with ⟨hM,hq,hr,hg,hf⟩
    exact ⟨rfl,rational_saturated_flow_completion_with_zeros q t F y M r ε hM hq hr hg hf⟩
  · cases ho

theorem rational_flow_certificate_completion_none_iff {m : ℕ} (q t : Fin m → ℚ)
    (M r ε : ℚ) (F : Fin m → Fin m → ℚ) (y : Fin m → ℚ) :
    rationalFlowCompletionFromCertificate q t M r ε F y = none ↔
      rationalFlowCertificateCheck q t M r ε F y ≠ true := by
  unfold rationalFlowCompletionFromCertificate
  split <;> simp_all

end SparseCompletion
