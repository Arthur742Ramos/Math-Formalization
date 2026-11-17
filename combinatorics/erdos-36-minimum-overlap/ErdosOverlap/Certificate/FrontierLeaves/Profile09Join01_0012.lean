/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join01_0012Claim : IntegralClaim := ⟨(506321/524288 : ℚ), (513583/524288 : ℚ), (-7179121109643942260457448594312)⟩

theorem profile09Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join01_0012Claim :=
  profile09Join00_0024Bound.glue profile09Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
