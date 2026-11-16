/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0002
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin03_0001Claim : IntegralClaim := ⟨(64435/4194304 : ℚ), (104735/262144 : ℚ), 351314088525090343343478503794893868765⟩

theorem denominatorJoin03_0001Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0001Claim :=
  denominatorJoin02_0002Bound.glue denominatorJoin02_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
