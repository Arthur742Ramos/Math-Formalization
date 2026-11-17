/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0002
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0001Claim : IntegralClaim := ⟨(1027/65536 : ℚ), (39/256 : ℚ), 0⟩

theorem centralJoin00_0001Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0001Claim :=
  centralBlock0002.glue centralBlock0003 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
