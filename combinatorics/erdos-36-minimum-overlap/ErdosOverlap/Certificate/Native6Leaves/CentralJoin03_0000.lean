/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.CentralBlock0008
public import ErdosOverlap.Certificate.Native6Leaves.CentralJoin02_0000

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin03_0000Claim : IntegralClaim :=
  ⟨(0/1 : ℚ), (1/1 : ℚ), (Int.ofNat 35944788761470441579151490023424)⟩

theorem centralJoin03_0000 :
  IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin03_0000Claim :=
  centralJoin02_0000.glue centralBlock0008 (by decide +kernel)

end
end ErdosOverlap.Native6Leaves
