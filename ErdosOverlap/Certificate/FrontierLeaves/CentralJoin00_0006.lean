/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0012
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0006Claim : IntegralClaim := ⟨(2879/5080 : ℚ), (21123/32768 : ℚ), 1052459336082966183755911489767⟩

theorem centralJoin00_0006Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0006Claim :=
  centralBlock0012.glue centralBlock0013 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
