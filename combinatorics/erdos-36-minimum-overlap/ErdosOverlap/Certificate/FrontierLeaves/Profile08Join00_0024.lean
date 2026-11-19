/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join00_0024Claim : IntegralClaim := ⟨(127357/131072 : ℚ), (1025825/1048576 : ℚ), (-3879515466823003466733665793249)⟩

theorem profile08Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0024Claim :=
  profile08Block0048.glue profile08Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
