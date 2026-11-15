/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0010
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0010 : IntegralClaim := ⟨(3503/131072 : ℚ), (12/59 : ℚ), (Int.ofNat 69460552349817357959366749007105753088)⟩

theorem denominatorBlock0010 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0010 :=
  denominatorBlock_certificate denominatorLeaves0010 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
