/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0014
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0007Claim : IntegralClaim := ⟨(3502137/4194304 : ℚ), (127673/131072 : ℚ), 13749937804505141640996943106848337529⟩

theorem denominatorJoin02_0007Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0007Claim :=
  denominatorJoin01_0014Bound.glue denominatorJoin01_0015Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
