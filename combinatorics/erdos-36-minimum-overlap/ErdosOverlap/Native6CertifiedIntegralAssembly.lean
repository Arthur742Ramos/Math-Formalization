/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Native6IntegralAssembly
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual
public import ErdosOverlap.Numerics.IntegralClaimFinal

/-!
# From completed native integral certificate trees to the rounded physical rows

The input certificates can be built from actual checked leaves and balanced
joins. Final rounding is an exact finite comparison of their integer totals.
No external integral enclosure or physical return is assumed here.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

open Numerics Native6Leaves

theorem nativeIntegralBounds_of_certificates
    (denominatorClaim centralClaim : IntegralClaim) (profileClaim : Fin 10 → IntegralClaim)
    (denominatorCertificate : IntegralClaim.UpperCertificate denominatorIntegrand
      (4*approximationError) denominatorClaim)
    (centralCertificate : IntegralClaim.LowerCertificate centralIntegrand
      (2*approximationError) centralClaim)
    (profileCertificate : ∀ mode : Fin 10,
      IntegralClaim.LowerCertificate (profileIntegrand mode) (2*approximationError) (profileClaim mode))
    (denominatorCheck : IntegralClaim.upperFinalCheck denominatorClaim
      (4*approximationError) nativeDenominatorBound = true)
    (centralCheck : IntegralClaim.lowerFinalCheck centralClaim
      (2*approximationError) centralIntegralLower = true)
    (profileCheck : ∀ mode : Fin 10, IntegralClaim.lowerFinalCheck (profileClaim mode)
      (2*approximationError) (profileIntegralLower mode) = true) : NativeIntegralBounds := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← integral_denominatorIntegrand]
    exact denominatorCertificate.full_bound denominatorCheck
  · exact centralCertificate.full_bound centralCheck
  · intro mode
    exact (profileCertificate mode).full_bound (profileCheck mode)

end ErdosOverlap.Certificate.CoarseNative6
