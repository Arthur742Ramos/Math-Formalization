/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0006
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0003Claim : IntegralClaim := ⟨(1503/131072 : ℚ), (64435/4194304 : ℚ), 6941592107787443043746096363013⟩

theorem denominatorJoin01_0003Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0003Claim :=
  denominatorJoin00_0006Bound.glue denominatorJoin00_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
