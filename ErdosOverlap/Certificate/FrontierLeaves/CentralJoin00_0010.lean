/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0020
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0021

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0010Claim : IntegralClaim := ⟨(786621/999424 : ℚ), (27851/32768 : ℚ), 0⟩

theorem centralJoin00_0010Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0010Claim :=
  centralBlock0020.glue centralBlock0021 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
