/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join00_0012Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (8021/16384 : ℚ), 6514659457531822322536597487114⟩

theorem profile13Join00_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0012Claim :=
  profile13Block0024.glue profile13Block0025 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
