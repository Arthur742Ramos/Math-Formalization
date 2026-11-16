/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0030
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0031

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join00_0015Claim : IntegralClaim := ⟨(77107/131072 : ℚ), (9289/14276 : ℚ), 817830468686537408978815160415⟩

theorem profile17Join00_0015Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join00_0015Claim :=
  profile17Block0030.glue profile17Block0031 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
