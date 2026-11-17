/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0014
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile18Join00_0007Claim : IntegralClaim := ⟨(2329/131072 : ℚ), (11173/524288 : ℚ), 0⟩

theorem profile18Join00_0007Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0007Claim :=
  profile18Block0014.glue profile18Block0015 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
