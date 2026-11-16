/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (127673/131072 : ℚ), 893948766761075701125280080669280719315⟩

theorem denominatorJoin05_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin05_0000Claim :=
  denominatorJoin04_0000Bound.glue denominatorJoin04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
