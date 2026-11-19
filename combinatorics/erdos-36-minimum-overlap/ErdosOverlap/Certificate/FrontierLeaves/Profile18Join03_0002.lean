/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile18Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (16263/16384 : ℚ), 991531825376777525972690711393⟩

theorem profile18Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join03_0002Claim :=
  profile18Join02_0004Bound.glue profile18Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
