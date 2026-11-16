/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0022
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0011Claim : IntegralClaim := ⟨(27851/32768 : ℚ), (29737/32768 : ℚ), 0⟩

theorem centralJoin00_0011Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0011Claim :=
  centralBlock0022.glue centralBlock0023 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
