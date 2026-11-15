/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0017
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0017 : IntegralClaim := ⟨(102133/198656 : ℚ), (1145/2048 : ℚ), (Int.ofNat 74344097537099502053200328070615007232)⟩

theorem denominatorBlock0017 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0017 :=
  denominatorBlock_certificate denominatorLeaves0017 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
