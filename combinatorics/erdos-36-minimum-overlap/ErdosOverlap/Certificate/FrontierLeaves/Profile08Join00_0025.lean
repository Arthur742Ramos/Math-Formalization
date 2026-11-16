/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0025Claim : IntegralClaim := ⟨(1025825/1048576 : ℚ), (129005/131072 : ℚ), (-2881658702034183125177486323424)⟩

theorem profile08Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0025Claim :=
  profile08Block0050.glue profile08Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
