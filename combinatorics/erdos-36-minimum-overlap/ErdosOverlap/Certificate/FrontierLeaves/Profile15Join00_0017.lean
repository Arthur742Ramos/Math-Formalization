/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0034
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0035

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile15Join00_0017Claim : IntegralClaim := ⟨(175441/262144 : ℚ), (1469/2048 : ℚ), 577686278291183560307924963535⟩

theorem profile15Join00_0017Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0017Claim :=
  profile15Block0034.glue profile15Block0035 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
