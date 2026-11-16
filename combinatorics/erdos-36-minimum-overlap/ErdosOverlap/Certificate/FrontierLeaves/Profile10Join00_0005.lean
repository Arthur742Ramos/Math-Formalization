/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join00_0005Claim : IntegralClaim := ⟨(12941/1048576 : ℚ), (15667/1048576 : ℚ), 0⟩

theorem profile10Join00_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join00_0005Claim :=
  profile10Block0010.glue profile10Block0011 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
