/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0028
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join02_0006

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join03_0003Claim : IntegralClaim := ⟨(506321/524288 : ℚ), (1/1 : ℚ), (-14544153801771484418700993361940)⟩

theorem profile09Join03_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join03_0003Claim :=
  profile09Join02_0006Bound.glue profile09Join00_0028Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
