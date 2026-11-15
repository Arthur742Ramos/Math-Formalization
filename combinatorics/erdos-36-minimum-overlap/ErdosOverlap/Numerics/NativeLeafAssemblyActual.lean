/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafAssembly
public import ErdosOverlap.Numerics.NativeLeafCertificateActual
public import ErdosOverlap.Numerics.IntegralClaimBlock

/-!
# Actual native block certificates for balanced finite assembly

Each block checks its own adjacent leaf chain and exact integer total.
Every approximation premise is discharged by the actual native polynomial
compiler. Subsequent joins use only the literal block claims and the small
`IntegralClaim.joinCheck`, without reopening the original leaf list.
-/

@[expose] public section

namespace ErdosOverlap.Native6Leaves

open Numerics

theorem profileBlock_certificate {mode : Fin 10} (leaves : List (CheckedProfileLeaf mode))
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (profileClaims leaves) = true)
    (hs : IntegralClaim.total (profileClaims leaves) = amount) :
    IntegralClaim.LowerCertificate (profileIntegrand mode) (2*approximationError)
      ⟨lo,hi,amount⟩ := by
  refine ⟨profileBlock_integrable leaves hc, ?_⟩
  exact profileBlock_lower leaves hc hs (fun leaf _ => leaf.val.geometry.approximation)

theorem centralBlock_certificate (leaves : List CheckedCentralLeaf)
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (centralClaims leaves) = true)
    (hs : IntegralClaim.total (centralClaims leaves) = amount) :
    IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) ⟨lo,hi,amount⟩ := by
  refine ⟨centralBlock_integrable leaves hc, ?_⟩
  exact centralBlock_lower leaves hc hs (fun leaf _ => leaf.val.geometry.approximation)

theorem denominatorBlock_certificate (leaves : List CheckedDenominatorLeaf)
    {lo hi : ℚ} {amount : ℤ}
    (hc : IntegralClaim.chainCheck lo hi (denominatorClaims leaves) = true)
    (hs : IntegralClaim.total (denominatorClaims leaves) = amount) :
    IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) ⟨lo,hi,amount⟩ := by
  refine ⟨denominatorBlock_integrable leaves hc, ?_⟩
  exact denominatorBlock_upper leaves hc hs (fun leaf _ => leaf.val.geometry.approximation)

end ErdosOverlap.Native6Leaves
