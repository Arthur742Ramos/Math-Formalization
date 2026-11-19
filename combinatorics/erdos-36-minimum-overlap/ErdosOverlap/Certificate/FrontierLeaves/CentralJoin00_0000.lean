/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0000
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1027/65536 : ℚ), 0⟩

theorem centralJoin00_0000Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0000Claim :=
  centralBlock0000.glue centralBlock0001 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
