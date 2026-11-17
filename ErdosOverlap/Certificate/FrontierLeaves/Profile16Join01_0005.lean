/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join00_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join00_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile16Join01_0005Claim : IntegralClaim := ⟨(7685/262144 : ℚ), (52715/131072 : ℚ), 24254719523713535848104075519248⟩

theorem profile16Join01_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join01_0005Claim :=
  profile16Join00_0010Bound.glue profile16Join00_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
