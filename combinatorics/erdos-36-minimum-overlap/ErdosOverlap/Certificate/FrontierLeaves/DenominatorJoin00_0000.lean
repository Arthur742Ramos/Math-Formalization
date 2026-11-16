/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (223/131072 : ℚ), 1396623143691771219889020903933⟩

theorem denominatorJoin00_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0000Claim :=
  denominatorBlock0000.glue denominatorBlock0001 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
