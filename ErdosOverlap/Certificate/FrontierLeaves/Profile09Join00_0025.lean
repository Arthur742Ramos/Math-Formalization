/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0025Claim : IntegralClaim := ⟨(127597/131072 : ℚ), (513583/524288 : ℚ), (-3466307014885917049958403300747)⟩

theorem profile09Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0025Claim :=
  profile09Block0050.glue profile09Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
