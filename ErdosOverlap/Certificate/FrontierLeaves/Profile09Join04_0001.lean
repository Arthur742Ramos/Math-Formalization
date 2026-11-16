/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join03_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join03_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), (-25989725128240798356110080150428)⟩

theorem profile09Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join04_0001Claim :=
  profile09Join03_0002Bound.glue profile09Join03_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
