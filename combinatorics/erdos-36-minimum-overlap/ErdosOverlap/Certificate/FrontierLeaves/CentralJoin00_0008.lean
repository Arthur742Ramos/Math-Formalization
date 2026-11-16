/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0016
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0008Claim : IntegralClaim := ⟨(88033/131072 : ℚ), (2985/4096 : ℚ), 432757108452865804793501464782⟩

theorem centralJoin00_0008Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0008Claim :=
  centralBlock0016.glue centralBlock0017 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
