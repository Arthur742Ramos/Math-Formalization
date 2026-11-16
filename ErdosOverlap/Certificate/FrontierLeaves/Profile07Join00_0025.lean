/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join00_0025Claim : IntegralClaim := ⟨(514723/524288 : ℚ), (129413/131072 : ℚ), (-2831592552076013860988244159032)⟩

theorem profile07Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0025Claim :=
  profile07Block0050.glue profile07Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
