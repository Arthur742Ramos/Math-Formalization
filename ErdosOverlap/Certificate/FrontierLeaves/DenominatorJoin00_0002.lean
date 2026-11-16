/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0004
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0002Claim : IntegralClaim := ⟨(479/131072 : ℚ), (735/131072 : ℚ), 1818325124416732779693376186469⟩

theorem denominatorJoin00_0002Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0002Claim :=
  denominatorBlock0004.glue denominatorBlock0005 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
