/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0026
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join00_0013Claim : IntegralClaim := ⟨(8021/16384 : ℚ), (1633327/3178496 : ℚ), 3614226122165908706398272135716⟩

theorem profile06Join00_0013Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0013Claim :=
  profile06Block0026.glue profile06Block0027 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
