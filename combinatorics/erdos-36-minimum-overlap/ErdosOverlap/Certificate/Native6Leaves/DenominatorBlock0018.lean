/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0018
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0018 : IntegralClaim := ⟨(1145/2048 : ℚ), (475031/794624 : ℚ), (Int.ofNat 57781542827328816981310545637601705984)⟩

theorem denominatorBlock0018 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0018 :=
  denominatorBlock_certificate denominatorLeaves0018 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
