/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0030
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0031

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join00_0015Claim : IntegralClaim := ⟨(77107/131072 : ℚ), (9289/14276 : ℚ), 817830468686537408978815160415⟩

theorem profile12Join00_0015Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join00_0015Claim :=
  profile12Block0030.glue profile12Block0031 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
