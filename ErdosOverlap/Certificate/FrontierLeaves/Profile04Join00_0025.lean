/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join00_0025Claim : IntegralClaim := ⟨(519729/524288 : ℚ), (1/1 : ℚ), (-1919774754810669582798084355796)⟩

theorem profile04Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0025Claim :=
  profile04Block0050.glue profile04Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
