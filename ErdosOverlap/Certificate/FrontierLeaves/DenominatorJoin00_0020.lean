/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0040
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0041

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0020Claim : IntegralClaim := ⟨(9283/16384 : ℚ), (5119191/8323072 : ℚ), 69600811604741825269628813516137256773⟩

theorem denominatorJoin00_0020Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0020Claim :=
  denominatorBlock0040.glue denominatorBlock0041 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
