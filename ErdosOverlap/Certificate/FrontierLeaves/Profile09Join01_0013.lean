/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0026
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join01_0013Claim : IntegralClaim := ⟨(513583/524288 : ℚ), (4128705/4161536 : ℚ), (-5516122764036805713568445936740)⟩

theorem profile09Join01_0013Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join01_0013Claim :=
  profile09Join00_0026Bound.glue profile09Join00_0027Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
