/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin03_0002
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin03_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin04_0001Claim : IntegralClaim := ⟨(104735/262144 : ℚ), (127673/131072 : ℚ), 542634661442655675925883858490092412298⟩

theorem denominatorJoin04_0001Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin04_0001Claim :=
  denominatorJoin03_0002Bound.glue denominatorJoin03_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
