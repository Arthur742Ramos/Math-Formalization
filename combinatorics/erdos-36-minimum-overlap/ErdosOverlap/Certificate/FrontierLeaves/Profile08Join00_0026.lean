/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0052
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0053

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0026Claim : IntegralClaim := ⟨(129005/131072 : ℚ), (259609/262144 : ℚ), (-2949793089296481880578099646635)⟩

theorem profile08Join00_0026Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0026Claim :=
  profile08Block0052.glue profile08Block0053 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
