/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralData0002
public import ErdosOverlap.Numerics.NativeLeafAssemblyActual

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralClaim0002 : IntegralClaim := ⟨(129/8192 : ℚ), (421/16384 : ℚ), (Int.negSucc 144115188075855871)⟩

theorem centralBlock0002 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralClaim0002 :=
  centralBlock_certificate centralLeaves0002 (by decide +kernel) (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
