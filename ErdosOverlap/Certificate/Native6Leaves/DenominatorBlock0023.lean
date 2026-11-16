/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0023
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0023 : IntegralClaim := ⟨(68307/94672 : ℚ), (786649/1040384 : ℚ), (Int.ofNat 23275517471326631328257584988541681664)⟩

theorem denominatorBlock0023 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0023 :=
  denominatorBlock_certificate denominatorLeaves0023 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
