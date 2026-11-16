/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0056
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0057

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join00_0028Claim : IntegralClaim := ⟨(4128705/4161536 : ℚ), (1/1 : ℚ), (-1848909928090736444675098830888)⟩

theorem profile09Join00_0028Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0028Claim :=
  profile09Block0056.glue profile09Block0057 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
