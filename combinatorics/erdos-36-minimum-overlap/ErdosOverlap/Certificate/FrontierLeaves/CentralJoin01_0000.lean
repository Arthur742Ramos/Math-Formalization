/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0000
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin01_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (39/256 : ℚ), 0⟩

theorem centralJoin01_0000Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0000Claim :=
  centralJoin00_0000Bound.glue centralJoin00_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
