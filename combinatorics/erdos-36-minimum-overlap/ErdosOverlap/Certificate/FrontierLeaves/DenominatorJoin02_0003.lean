/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0006
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0003Claim : IntegralClaim := ⟨(51257/2097152 : ℚ), (104735/262144 : ℚ), 351314075773902606109521295212024009416⟩

theorem denominatorJoin02_0003Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0003Claim :=
  denominatorJoin01_0006Bound.glue denominatorJoin01_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
