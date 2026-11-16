/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0054
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0055

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0027Claim : IntegralClaim := ⟨(1033441/1048576 : ℚ), (4128705/4161536 : ℚ), (-2648560719649341459893168949967)⟩

theorem profile09Join00_0027Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0027Claim :=
  profile09Block0054.glue profile09Block0055 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
