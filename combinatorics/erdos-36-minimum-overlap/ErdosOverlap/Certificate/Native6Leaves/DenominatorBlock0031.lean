/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0031
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0031 : IntegralClaim := ⟨(32617/32768 : ℚ), (1/1 : ℚ), (Int.ofNat 150622192748503429136526514061312)⟩

theorem denominatorBlock0031 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0031 :=
  denominatorBlock_certificate denominatorLeaves0031 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
