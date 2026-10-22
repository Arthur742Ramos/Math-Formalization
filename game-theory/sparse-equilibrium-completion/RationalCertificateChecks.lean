/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalCertificateSoundness
public meta import RationalCertificate
@[expose] public section
namespace SparseCompletion
/-- Empty residual support is valid data; omitted residual actions still respond. -/
def certificateEmptySupport : RationalCertificate 1 1 :=
  ⟨∅,fun _ => 1,
    (fun i => False.elim (Finset.notMem_empty i.val i.property)),
    (fun i _ => False.elim (Finset.notMem_empty i.val i.property))⟩

#guard certificateEmptySupport.check (fun _ _ => 0) (fun _ _ => 0) 1 0 = true
#guard certificateEmptySupport.check (fun _ _ => 0) (fun _ _ => 1) 1 0 = false

#print axioms RationalCertificate.check_iff
#print axioms RationalCertificate.q_on
#print axioms RationalCertificate.b_on
#print axioms RationalCertificate.reject_omitted_violation
#print axioms RationalCertificate.realQ_off
#print axioms RationalCertificate.support_card_le
#print axioms RationalCertificate.realB_stored
#print axioms RationalCertificate.realB_omitted
#print axioms RationalCertificate.rows_iff
#print axioms RationalCertificate.accepted_full_game
#print axioms RationalCertificate.check_iff_full_rows
end SparseCompletion
