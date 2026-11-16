/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0023Claim : IntegralClaim := ⟨(16037/16384 : ℚ), (2017/2048 : ℚ), (-2877861556460847174788469957157)⟩

theorem profile04Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0023Claim :=
  profile04Block0046.glue profile04Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
