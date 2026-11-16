/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0052
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0053

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join00_0026Claim : IntegralClaim := ⟨(129413/131072 : ℚ), (521877/524288 : ℚ), (-1837372508726446743733640353625)⟩

theorem profile07Join00_0026Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0026Claim :=
  profile07Block0052.glue profile07Block0053 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
