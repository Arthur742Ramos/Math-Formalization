/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin00_0000
public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin00_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin01_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (139/512 : ℚ), (Int.ofNat 57942863479733444462210187264)⟩

theorem centralJoin01_0000 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0000Claim :=
  centralJoin00_0000.glue centralJoin00_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
