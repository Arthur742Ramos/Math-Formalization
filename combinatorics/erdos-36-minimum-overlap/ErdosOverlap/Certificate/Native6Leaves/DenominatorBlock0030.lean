/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0030
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0030 : IntegralClaim := ⟨(15959/16384 : ℚ), (32617/32768 : ℚ), (Int.ofNat 53686906254537569311267913516187648)⟩

theorem denominatorBlock0030 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0030 :=
  denominatorBlock_certificate denominatorLeaves0030 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
