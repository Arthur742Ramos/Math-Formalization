/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralData0008
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralClaim0008 : IntegralClaim := ⟨(60/61 : ℚ), (1/1 : ℚ), (Int.negSucc 105271641289785343)⟩

theorem centralBlock0008 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralClaim0008 :=
  centralBlock_certificate centralLeaves0008 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
