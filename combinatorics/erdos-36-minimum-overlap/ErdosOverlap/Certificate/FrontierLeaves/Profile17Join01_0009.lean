/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0018
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join01_0009Claim : IntegralClaim := ⟨(1469/2048 : ℚ), (54239/65536 : ℚ), 112811916706285986214655679176⟩

theorem profile17Join01_0009Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join01_0009Claim :=
  profile17Join00_0018Bound.glue profile17Join00_0019Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
