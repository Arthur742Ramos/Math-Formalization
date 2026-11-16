/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0042
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0043

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0021Claim : IntegralClaim := ⟨(891/1024 : ℚ), (135183/145408 : ℚ), 0⟩

theorem profile08Join00_0021Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0021Claim :=
  profile08Block0042.glue profile08Block0043 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
