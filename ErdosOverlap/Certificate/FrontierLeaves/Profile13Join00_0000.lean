/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join00_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (583/262144 : ℚ), 0⟩

theorem profile13Join00_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0000Claim :=
  profile13Block0000.glue profile13Block0001 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
