/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0020
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0021

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0010Claim : IntegralClaim := ⟨(9283/16384 : ℚ), (42757/65536 : ℚ), 115454348912686390950667048630217115812⟩

theorem denominatorJoin01_0010Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0010Claim :=
  denominatorJoin00_0020Bound.glue denominatorJoin00_0021Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
