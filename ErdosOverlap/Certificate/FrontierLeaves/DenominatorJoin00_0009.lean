/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0018
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0009Claim : IntegralClaim := ⟨(18349/1048576 : ℚ), (5349/262144 : ℚ), 2902546712078241762212095009581⟩

theorem denominatorJoin00_0009Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0009Claim :=
  denominatorBlock0018.glue denominatorBlock0019 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
