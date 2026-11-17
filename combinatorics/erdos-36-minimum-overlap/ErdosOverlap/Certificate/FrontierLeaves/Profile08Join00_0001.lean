/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join00_0001Claim : IntegralClaim := ⟨(583/262144 : ℚ), (4749/1048576 : ℚ), 0⟩

theorem profile08Join00_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0001Claim :=
  profile08Block0002.glue profile08Block0003 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
