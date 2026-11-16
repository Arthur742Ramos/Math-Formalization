/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join01_0012Claim : IntegralClaim := ⟨(128771/131072 : ℚ), (130581/131072 : ℚ), (-4341539276212893154595330888412)⟩

theorem profile05Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join01_0012Claim :=
  profile05Join00_0024Bound.glue profile05Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
