/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join00_0024Claim : IntegralClaim := ⟨(130089/131072 : ℚ), (1/1 : ℚ), (-4067890722443454389188324428)⟩

theorem profile12Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join00_0024Claim :=
  profile12Block0048.glue profile12Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
