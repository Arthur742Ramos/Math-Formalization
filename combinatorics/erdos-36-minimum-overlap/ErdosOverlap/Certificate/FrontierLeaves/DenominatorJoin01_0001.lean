/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0002
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0001Claim : IntegralClaim := ⟨(479/131072 : ℚ), (991/131072 : ℚ), 3297865186861274936944400385810⟩

theorem denominatorJoin01_0001Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0001Claim :=
  denominatorJoin00_0002Bound.glue denominatorJoin00_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
