/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0002
public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0001Claim : IntegralClaim :=
  ⟨(129/8192 : ℚ), (139/512 : ℚ), (Int.ofNat 57942863480021674838361899008)⟩

theorem centralJoin00_0001 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0001Claim :=
  centralBlock0002.glue centralBlock0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
