/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0048
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0024Claim : IntegralClaim := ⟨(40973/60416 : ℚ), (1050109/1458176 : ℚ), 36903022939072453454932024314221953993⟩

theorem denominatorJoin00_0024Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0024Claim :=
  denominatorBlock0048.glue denominatorBlock0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
