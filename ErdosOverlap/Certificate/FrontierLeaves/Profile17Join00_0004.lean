/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join00_0004Claim : IntegralClaim := ⟨(319/32768 : ℚ), (12941/1048576 : ℚ), 0⟩

theorem profile17Join00_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join00_0004Claim :=
  profile17Block0008.glue profile17Block0009 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
