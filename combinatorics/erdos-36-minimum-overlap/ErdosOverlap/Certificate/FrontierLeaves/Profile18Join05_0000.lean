/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile18Join05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 38003428231863816804984809174402⟩

theorem profile18Join05_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join05_0000Claim :=
  profile18Join04_0000Bound.glue profile18Join04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
