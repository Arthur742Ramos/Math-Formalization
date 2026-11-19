/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile05Join01_0001Claim : IntegralClaim := ⟨(4749/1048576 : ℚ), (319/32768 : ℚ), 0⟩

theorem profile05Join01_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join01_0001Claim :=
  profile05Join00_0002Bound.glue profile05Join00_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
