/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (506321/524288 : ℚ), (-11445571326469313937409086788488)⟩

theorem profile09Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join03_0002Claim :=
  profile09Join02_0004Bound.glue profile09Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
