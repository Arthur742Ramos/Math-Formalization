/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0036
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0037

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join00_0018Claim : IntegralClaim := ⟨(1469/2048 : ℚ), (3151/4096 : ℚ), 112811916706285986214655679176⟩

theorem profile07Join00_0018Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0018Claim :=
  profile07Block0036.glue profile07Block0037 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
