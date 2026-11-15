/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin01_0000
public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin01_0001

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin02_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (60/61 : ℚ), (Int.ofNat 35944788761470546850792779808768)⟩

theorem centralJoin02_0000 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin02_0000Claim :=
  centralJoin01_0000.glue centralJoin01_0001 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
