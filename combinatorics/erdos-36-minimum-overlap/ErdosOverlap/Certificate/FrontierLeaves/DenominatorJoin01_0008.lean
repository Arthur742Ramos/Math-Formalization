/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0016
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0008Claim : IntegralClaim := ⟨(104735/262144 : ℚ), (65487/131072 : ℚ), 180693640615793169159489682429524731286⟩

theorem denominatorJoin01_0008Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0008Claim :=
  denominatorJoin00_0016Bound.glue denominatorJoin00_0017Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
