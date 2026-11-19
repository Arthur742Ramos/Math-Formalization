/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0026
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin00_0013Claim : IntegralClaim := ⟨(7955/8192 : ℚ), (1/1 : ℚ), 0⟩

theorem centralJoin00_0013Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0013Claim :=
  centralBlock0026.glue centralBlock0027 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
