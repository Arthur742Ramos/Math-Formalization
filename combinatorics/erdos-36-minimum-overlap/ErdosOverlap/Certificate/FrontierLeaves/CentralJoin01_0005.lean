/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0010
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin01_0005Claim : IntegralClaim := ⟨(786621/999424 : ℚ), (29737/32768 : ℚ), 0⟩

theorem centralJoin01_0005Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0005Claim :=
  centralJoin00_0010Bound.glue centralJoin00_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
