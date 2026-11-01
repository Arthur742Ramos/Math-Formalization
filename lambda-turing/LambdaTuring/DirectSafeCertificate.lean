/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectCertificateValidatorCode
public meta import LambdaTuring.DirectCertificateValidatorCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

theorem betaCertificateRunCode_any (term paths : Nat) :
    betaCertificateRunCode.eval (Nat.pair term paths) =
      Part.some (betaTraceIterValue paths (Nat.pair (term + 1) paths)).unpair.1 := by
  let input := Nat.pair term paths
  have ht : Code.eval .left input = Part.some term := by simp [input, Code.eval]
  have hp : Code.eval .right input = Part.some paths := by simp [input, Code.eval]
  have ht' := evalCompSome .succ .left _ _ _ ht (show Code.eval .succ term = Part.some (term + 1) from rfl)
  have hstate := evalPairSome (.comp .succ .left) .right _ _ _ ht' hp
  have harg := evalPairSome (.pair (.comp .succ .left) .right) .right _ _ _ hstate hp
  have hrun := betaTraceIterCode_eval (Nat.pair (term + 1) paths) paths
  have hiter := evalCompSome betaTraceIterCode _ _ _ _ harg hrun
  exact evalCompSome .left _ _ _ _ hiter
    (show Code.eval .left (betaTraceIterValue paths (Nat.pair (term + 1) paths)) =
      Part.some (betaTraceIterValue paths (Nat.pair (term + 1) paths)).unpair.1 from rfl)

def safeCertificateCode : Code := chooseZeroCode (.comp encodedCertificateValidCode .right) .zero betaCertificateRunCode

theorem safeCertificateCode_eval (term cert : Nat) :
    safeCertificateCode.eval (Nat.pair term cert) =
      Part.some (if encodedCertificateValid cert then
        (betaTraceIterValue cert (Nat.pair (term + 1) cert)).unpair.1 else 0) := by
  let input := Nat.pair term cert
  have hp : Code.eval .right input = Part.some cert := by simp [input, Code.eval]
  have hv := evalCompSome encodedCertificateValidCode .right _ _ _ hp (encodedCertificateValidCode_eval cert)
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hr := betaCertificateRunCode_any term cert
  have h := chooseZeroCode_eval (.comp encodedCertificateValidCode .right) .zero betaCertificateRunCode
    _ _ _ _ hv hz hr
  cases hb : encodedCertificateValid cert <;> simpa [safeCertificateCode, boolFlag, hb] using h

theorem safeCertificateCode_valid (t : Term) (paths : List (List Bool)) :
    safeCertificateCode.eval (Nat.pair (directTermNumber t) (Encodable.encode paths)) =
      Part.some (Encodable.encode ((betaRun paths t).map directTermNumber)) := by
  have hv : encodedCertificateValid (Encodable.encode paths) = true :=
    (encodedCertificateValid_spec _).2 ⟨paths, rfl⟩
  have h := betaCertificateRunCode_eval t paths
  rw [betaCertificateRunCode_any] at h
  rw [safeCertificateCode_eval, hv]
  exact h

theorem safeCertificateCode_invalid (t cert : Nat)
    (h : ¬ ∃ paths : List (List Bool), Encodable.encode paths = cert) :
    safeCertificateCode.eval (Nat.pair t cert) = Part.some 0 := by
  have hv : encodedCertificateValid cert = false := by
    cases he : encodedCertificateValid cert with
    | false => rfl
    | true => exact False.elim (h ((encodedCertificateValid_spec cert).1 he))
  simp [safeCertificateCode_eval, hv]

theorem safeCertificateCode_sound (t : Term) (cert number : Nat)
    (h : safeCertificateCode.eval (Nat.pair (directTermNumber t) cert) = Part.some (number + 1)) :
    ∃ u : Term, Reaches t u ∧ directTermNumber u = number := by
  by_cases hv : ∃ paths : List (List Bool), Encodable.encode paths = cert
  · obtain ⟨paths, rfl⟩ := hv
    rw [safeCertificateCode_valid] at h
    cases hr : betaRun paths t with
    | none => simp [hr] at h
    | some u =>
      simp [hr] at h
      exact ⟨u, betaRun_sound hr, h⟩
  · rw [safeCertificateCode_invalid _ _ hv] at h
    simp at h

#print axioms safeCertificateCode
#print axioms safeCertificateCode_sound
end LambdaTuring
