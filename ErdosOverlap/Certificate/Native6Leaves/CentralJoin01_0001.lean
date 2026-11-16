/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin00_0002
public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin00_0003

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin01_0001Claim : IntegralClaim :=
  ⟨(139/512 : ℚ), (60/61 : ℚ), (Int.ofNat 35886845897990813406330569621504)⟩

theorem centralJoin01_0001 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0001Claim :=
  centralJoin00_0002.glue centralJoin00_0003 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
