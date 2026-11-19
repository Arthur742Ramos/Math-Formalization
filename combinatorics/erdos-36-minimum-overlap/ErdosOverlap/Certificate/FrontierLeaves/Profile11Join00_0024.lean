/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile11Join00_0024Claim : IntegralClaim := ⟨(130329/131072 : ℚ), (1/1 : ℚ), (-2832742961930769235572621906)⟩

theorem profile11Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Join00_0024Claim :=
  profile11Block0048.glue profile11Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
