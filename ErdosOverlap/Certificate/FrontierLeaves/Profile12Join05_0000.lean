/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 38003133634917916991892688513043⟩

theorem profile12Join05_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join05_0000Claim :=
  profile12Join04_0000Bound.glue profile12Join04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
