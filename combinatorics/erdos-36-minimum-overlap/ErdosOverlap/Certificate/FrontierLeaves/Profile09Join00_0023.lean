/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0023Claim : IntegralClaim := ⟨(251337/262144 : ℚ), (506321/524288 : ℚ), (-5193422970274861687071997481796)⟩

theorem profile09Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0023Claim :=
  profile09Block0046.glue profile09Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
