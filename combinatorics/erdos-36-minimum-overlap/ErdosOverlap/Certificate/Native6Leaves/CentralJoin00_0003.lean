/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0006
public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0007

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0003Claim : IntegralClaim :=
  ⟨(43651/65536 : ℚ), (60/61 : ℚ), (Int.ofNat 888720868309539330959976955904)⟩

theorem centralJoin00_0003 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0003Claim :=
  centralBlock0006.glue centralBlock0007 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
