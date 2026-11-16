/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin03_0000
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin03_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin04_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 38009851047321136842291162022795⟩

theorem centralJoin04_0000Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin04_0000Claim :=
  centralJoin03_0000Bound.glue centralJoin03_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
