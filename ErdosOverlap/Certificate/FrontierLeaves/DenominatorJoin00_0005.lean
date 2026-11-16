/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0010
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0005Claim : IntegralClaim := ⟨(1247/131072 : ℚ), (1503/131072 : ℚ), 1410784651751464045588232940779⟩

theorem denominatorJoin00_0005Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0005Claim :=
  denominatorBlock0010.glue denominatorBlock0011 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
