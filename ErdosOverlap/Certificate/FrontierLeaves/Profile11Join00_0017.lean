/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0034
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0035

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile11Join00_0017Claim : IntegralClaim := ⟨(175441/262144 : ℚ), (1469/2048 : ℚ), 577686278291183560307924963535⟩

theorem profile11Join00_0017Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Join00_0017Claim :=
  profile11Block0034.glue profile11Block0035 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
