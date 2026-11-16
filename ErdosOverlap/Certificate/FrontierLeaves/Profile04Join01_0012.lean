/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join01_0012Claim : IntegralClaim := ⟨(2017/2048 : ℚ), (1/1 : ℚ), (-4821313857096494854884223545596)⟩

theorem profile04Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join01_0012Claim :=
  profile04Join00_0024Bound.glue profile04Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
