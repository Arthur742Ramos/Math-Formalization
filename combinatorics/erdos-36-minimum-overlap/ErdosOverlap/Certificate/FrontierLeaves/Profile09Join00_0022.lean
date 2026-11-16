/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (251337/262144 : ℚ), (-7246962597534414269982366803700)⟩

theorem profile09Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0022Claim :=
  profile09Block0044.glue profile09Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
