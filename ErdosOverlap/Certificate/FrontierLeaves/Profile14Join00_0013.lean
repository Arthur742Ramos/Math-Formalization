/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0026
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join00_0013Claim : IntegralClaim := ⟨(8021/16384 : ℚ), (1633327/3178496 : ℚ), 3614226122165908706398272135716⟩

theorem profile14Join00_0013Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0013Claim :=
  profile14Block0026.glue profile14Block0027 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
