/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join00_0004Claim : IntegralClaim := ⟨(319/32768 : ℚ), (12941/1048576 : ℚ), 0⟩

theorem profile13Join00_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0004Claim :=
  profile13Block0008.glue profile13Block0009 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
