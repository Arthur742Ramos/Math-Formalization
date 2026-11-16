/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0046
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0023Claim : IntegralClaim := ⟨(87351/131072 : ℚ), (40973/60416 : ℚ), 12026234226675671904328409702322217643⟩

theorem denominatorJoin00_0023Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0023Claim :=
  denominatorBlock0046.glue denominatorBlock0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
