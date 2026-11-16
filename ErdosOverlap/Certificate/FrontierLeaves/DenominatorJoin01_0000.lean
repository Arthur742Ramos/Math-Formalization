/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (479/131072 : ℚ), 3638045745490804520044042727661⟩

theorem denominatorJoin01_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0000Claim :=
  denominatorJoin00_0000Bound.glue denominatorJoin00_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
