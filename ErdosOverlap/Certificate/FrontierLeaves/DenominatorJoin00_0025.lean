/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0050
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0025Claim : IntegralClaim := ⟨(1050109/1458176 : ℚ), (12339/16384 : ℚ), 22531583596343128577936780343999253694⟩

theorem denominatorJoin00_0025Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0025Claim :=
  denominatorBlock0050.glue denominatorBlock0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
