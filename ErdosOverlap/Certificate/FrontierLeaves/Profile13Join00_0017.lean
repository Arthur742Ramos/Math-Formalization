/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0034
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0035

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join00_0017Claim : IntegralClaim := ⟨(175441/262144 : ℚ), (1469/2048 : ℚ), 577686278291183560307924963535⟩

theorem profile13Join00_0017Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0017Claim :=
  profile13Block0034.glue profile13Block0035 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
