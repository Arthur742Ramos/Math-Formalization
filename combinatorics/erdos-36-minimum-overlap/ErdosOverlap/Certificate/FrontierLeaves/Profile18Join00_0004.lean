/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join00_0004Claim : IntegralClaim := ⟨(319/32768 : ℚ), (12941/1048576 : ℚ), 0⟩

theorem profile18Join00_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0004Claim :=
  profile18Block0008.glue profile18Block0009 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
