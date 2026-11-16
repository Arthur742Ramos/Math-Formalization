/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0038
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0039

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join00_0019Claim : IntegralClaim := ⟨(3151/4096 : ℚ), (54239/65536 : ℚ), 0⟩

theorem profile10Join00_0019Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join00_0019Claim :=
  profile10Block0038.glue profile10Block0039 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
