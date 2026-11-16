/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0012
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin01_0006Claim : IntegralClaim := ⟨(29737/32768 : ℚ), (1/1 : ℚ), 0⟩

theorem centralJoin01_0006Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0006Claim :=
  centralJoin00_0012Bound.glue centralJoin00_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
