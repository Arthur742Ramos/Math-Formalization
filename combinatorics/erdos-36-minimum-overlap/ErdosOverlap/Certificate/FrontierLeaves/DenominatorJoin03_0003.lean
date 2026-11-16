/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0006
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin03_0003Claim : IntegralClaim := ⟨(40973/60416 : ℚ), (127673/131072 : ℚ), 107829114375028176962000775465750644956⟩

theorem denominatorJoin03_0003Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0003Claim :=
  denominatorJoin02_0006Bound.glue denominatorJoin02_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
