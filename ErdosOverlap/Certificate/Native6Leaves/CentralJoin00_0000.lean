/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0000
public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (129/8192 : ℚ), (Int.negSucc 288230376151711743)⟩

theorem centralJoin00_0000 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0000Claim :=
  centralBlock0000.glue centralBlock0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
