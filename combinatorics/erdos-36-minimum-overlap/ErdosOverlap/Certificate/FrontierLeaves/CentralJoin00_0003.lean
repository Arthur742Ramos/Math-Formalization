/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0006
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0003Claim : IntegralClaim := ⟨(11731/32768 : ℚ), (106311/241664 : ℚ), 8080866209392392572963645289261⟩

theorem centralJoin00_0003Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0003Claim :=
  centralBlock0006.glue centralBlock0007 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
