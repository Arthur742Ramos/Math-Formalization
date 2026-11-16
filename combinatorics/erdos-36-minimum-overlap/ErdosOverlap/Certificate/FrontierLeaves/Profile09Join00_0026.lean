/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0052
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0053

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0026Claim : IntegralClaim := ⟨(513583/524288 : ℚ), (1033441/1048576 : ℚ), (-2867562044387464253675276986773)⟩

theorem profile09Join00_0026Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0026Claim :=
  profile09Block0052.glue profile09Block0053 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
