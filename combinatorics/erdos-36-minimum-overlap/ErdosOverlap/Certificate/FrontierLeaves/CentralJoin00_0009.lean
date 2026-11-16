/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0018
public import ErdosOverlap.Certificate.FrontierLeaves.CentralBlock0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin00_0009Claim : IntegralClaim := ⟨(2985/4096 : ℚ), (786621/999424 : ℚ), 44568264569130620627599506054⟩

theorem centralJoin00_0009Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin00_0009Claim :=
  centralBlock0018.glue centralBlock0019 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
