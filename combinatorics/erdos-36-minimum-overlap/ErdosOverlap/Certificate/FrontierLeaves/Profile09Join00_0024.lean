/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0024Claim : IntegralClaim := ⟨(506321/524288 : ℚ), (127597/131072 : ℚ), (-3712814094758025210499045293565)⟩

theorem profile09Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0024Claim :=
  profile09Block0048.glue profile09Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
