/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), 988019729706276465966899597277⟩

theorem profile14Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join04_0001Claim :=
  profile14Join03_0002Bound.glue profile14Join00_0024Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
