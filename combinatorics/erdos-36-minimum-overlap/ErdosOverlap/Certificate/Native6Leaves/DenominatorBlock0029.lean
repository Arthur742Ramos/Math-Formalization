/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.DenominatorData0029
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim0029 : IntegralClaim := ⟨(62417/65536 : ℚ), (15959/16384 : ℚ), (Int.ofNat 245773415963966952798704751899312128)⟩

theorem denominatorBlock0029 :
  IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim0029 :=
  denominatorBlock_certificate denominatorLeaves0029 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
