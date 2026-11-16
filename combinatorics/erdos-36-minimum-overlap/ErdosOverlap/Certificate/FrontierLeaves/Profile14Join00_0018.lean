/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0036
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0037

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join00_0018Claim : IntegralClaim := ⟨(1469/2048 : ℚ), (3151/4096 : ℚ), 112811916706285986214655679176⟩

theorem profile14Join00_0018Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0018Claim :=
  profile14Block0036.glue profile14Block0037 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
