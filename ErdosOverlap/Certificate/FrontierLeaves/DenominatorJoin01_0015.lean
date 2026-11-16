/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0030
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0031

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0015Claim : IntegralClaim := ⟨(1868035/2097152 : ℚ), (127673/131072 : ℚ), 3705887332878103632295496987964984458⟩

theorem denominatorJoin01_0015Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0015Claim :=
  denominatorJoin00_0030Bound.glue denominatorJoin00_0031Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
