/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile19Join00_0024Claim : IntegralClaim := ⟨(16265/16384 : ℚ), (1/1 : ℚ), (-3761542960349796091332433435)⟩

theorem profile19Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join00_0024Claim :=
  profile19Block0048.glue profile19Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
