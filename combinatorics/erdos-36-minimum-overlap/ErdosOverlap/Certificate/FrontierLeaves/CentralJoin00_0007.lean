/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0014
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0007Claim : IntegralClaim := ⟨(21123/32768 : ℚ), (88033/131072 : ℚ), 588845686518182867804892040712⟩

theorem centralJoin00_0007Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0007Claim :=
  centralBlock0014.glue centralBlock0015 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
