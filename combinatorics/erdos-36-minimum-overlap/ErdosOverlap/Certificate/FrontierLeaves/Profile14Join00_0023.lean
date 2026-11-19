/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile14Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (16269/16384 : ℚ), (-3161844382544056432916158350)⟩

theorem profile14Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0023Claim :=
  profile14Block0046.glue profile14Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
