/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0025
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0025 : IntegralClaim := ⟨(278563/352256 : ℚ), (217361/260096 : ℚ), (Int.ofNat 15426447806045915628734564945950146560)⟩

theorem denominatorBlock0025 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0025 :=
  denominatorBlock_certificate denominatorLeaves0025 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
