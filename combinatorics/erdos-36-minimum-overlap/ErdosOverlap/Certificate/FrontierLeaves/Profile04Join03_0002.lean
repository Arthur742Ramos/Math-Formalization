/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (2017/2048 : ℚ), (-1913286084872775308897547909425)⟩

theorem profile04Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join03_0002Claim :=
  profile04Join02_0004Bound.glue profile04Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
