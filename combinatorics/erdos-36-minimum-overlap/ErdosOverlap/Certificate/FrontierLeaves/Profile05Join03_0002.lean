/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile05Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (128771/131072 : ℚ), (-2406172517074979177900231729056)⟩

theorem profile05Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join03_0002Claim :=
  profile05Join02_0004Bound.glue profile05Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
