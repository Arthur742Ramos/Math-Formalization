/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0038
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0039

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join00_0019Claim : IntegralClaim := ⟨(3151/4096 : ℚ), (54239/65536 : ℚ), 0⟩

theorem profile14Join00_0019Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0019Claim :=
  profile14Block0038.glue profile14Block0039 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
