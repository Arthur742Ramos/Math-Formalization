/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join00_0012Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (8021/16384 : ℚ), 6514659457531822322536597487114⟩

theorem profile12Join00_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join00_0012Claim :=
  profile12Block0024.glue profile12Block0025 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
