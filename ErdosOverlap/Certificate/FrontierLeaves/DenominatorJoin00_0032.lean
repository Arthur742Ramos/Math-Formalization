/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0064
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0065

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0032Claim : IntegralClaim := ⟨(127673/131072 : ℚ), (1/1 : ℚ), 53803742815377420481864401871624924⟩

theorem denominatorJoin00_0032Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0032Claim :=
  denominatorBlock0064.glue denominatorBlock0065 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
