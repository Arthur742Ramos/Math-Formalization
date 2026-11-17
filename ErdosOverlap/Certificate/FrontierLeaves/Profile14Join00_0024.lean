/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile14Join00_0024Claim : IntegralClaim := ⟨(16269/16384 : ℚ), (1/1 : ℚ), (-3632667251141497245461741381)⟩

theorem profile14Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0024Claim :=
  profile14Block0048.glue profile14Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
