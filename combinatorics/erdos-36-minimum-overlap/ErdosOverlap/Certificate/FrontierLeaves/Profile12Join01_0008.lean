/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join00_0016
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join00_0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join01_0008Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1469/2048 : ℚ), 882002324633676033430621817832⟩

theorem profile12Join01_0008Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join01_0008Claim :=
  profile12Join00_0016Bound.glue profile12Join00_0017Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
