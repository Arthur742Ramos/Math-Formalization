/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0002
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0001Claim : IntegralClaim := ⟨(991/131072 : ℚ), (64435/4194304 : ℚ), 9857418749503838261395851324781⟩

theorem denominatorJoin02_0001Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0001Claim :=
  denominatorJoin01_0002Bound.glue denominatorJoin01_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
