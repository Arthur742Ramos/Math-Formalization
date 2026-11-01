/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectSafeCertificate
public meta import LambdaTuring.DirectSafeCertificate

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

def safeCertificateValue (term cert : Nat) : Nat :=
  if encodedCertificateValid cert then (betaTraceIterValue cert (Nat.pair (term + 1) cert)).unpair.1 else 0

def certificateObservation (term cert : Nat) : Option Nat :=
  let result := safeCertificateValue term cert
  if result = 0 then none else directChurchSearch result.pred (result.pred + 1)

def certificateObservationCode : Code := chooseZeroCode safeCertificateCode .zero
  (.comp directChurchDecodeCode (.comp predCode safeCertificateCode))

theorem certificateObservationCode_eval (term cert : Nat) :
    certificateObservationCode.eval (Nat.pair term cert) =
      Part.some (Encodable.encode (certificateObservation term cert)) := by
  let input := Nat.pair term cert
  let result := safeCertificateValue term cert
  have hs : safeCertificateCode.eval input = Part.some result := safeCertificateCode_eval term cert
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hp := evalCompSome predCode safeCertificateCode _ _ _ hs (eval_predCode result)
  have hd := evalCompSome directChurchDecodeCode (.comp predCode safeCertificateCode) _ _ _ hp
    (directChurchDecodeCode_eval result.pred)
  have h := chooseZeroCode_eval safeCertificateCode .zero
    (.comp directChurchDecodeCode (.comp predCode safeCertificateCode)) _ _ _ _ hs hz hd
  change certificateObservationCode.eval input = Part.some
    (Encodable.encode (if result = 0 then Option.none else directChurchSearch result.pred (result.pred + 1)))
  by_cases he : result = 0 <;>
    simpa [certificateObservationCode, he] using h

theorem certificateObservation_valid (t : Term) (paths : List (List Bool)) :
    certificateObservation (directTermNumber t) (Encodable.encode paths) =
      (betaRun paths t).bind decodeChurch := by
  have h := safeCertificateCode_valid t paths
  rw [safeCertificateCode_eval] at h
  have hvalue : safeCertificateValue (directTermNumber t) (Encodable.encode paths) =
      Encodable.encode ((betaRun paths t).map directTermNumber) := Part.some_injective h
  unfold certificateObservation
  rw [hvalue]
  cases hr : betaRun paths t with
  | none => simp
  | some u => simp [directChurchSearch_eq_decodeChurch]

theorem certificateObservation_invalid (term cert : Nat)
    (h : ¬ ∃ paths : List (List Bool), Encodable.encode paths = cert) :
    certificateObservation term cert = Option.none := by
  have hs := safeCertificateCode_invalid term cert h
  rw [safeCertificateCode_eval] at hs
  have hv : safeCertificateValue term cert = 0 := Part.some_injective hs
  simp [certificateObservation, hv]

theorem certificateObservation_iff (t : Term) (m : Nat) :
    (∃ cert, certificateObservation (directTermNumber t) cert = some m) ↔ Reaches t (church m) := by
  constructor
  · rintro ⟨cert, h⟩
    by_cases hv : ∃ paths : List (List Bool), Encodable.encode paths = cert
    · obtain ⟨paths, rfl⟩ := hv
      rw [certificateObservation_valid] at h
      obtain ⟨u, hu, hm⟩ := Option.bind_eq_some_iff.1 h
      have heq := (decodeChurch_iff u m).1 hm
      rw [← heq]
      exact betaRun_sound hu
    · rw [certificateObservation_invalid _ _ hv] at h
      contradiction
  · intro h
    obtain ⟨paths, hp⟩ := betaRun_complete h
    refine ⟨Encodable.encode paths, ?_⟩
    simp [certificateObservation_valid, hp, decodeChurch_iff]

#print axioms certificateObservationCode
#print axioms certificateObservation_iff
end LambdaTuring
