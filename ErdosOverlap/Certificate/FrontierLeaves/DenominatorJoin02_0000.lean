/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (991/131072 : ℚ), 6935910932352079456988443113471⟩

theorem denominatorJoin02_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0000Claim :=
  denominatorJoin01_0000Bound.glue denominatorJoin01_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
