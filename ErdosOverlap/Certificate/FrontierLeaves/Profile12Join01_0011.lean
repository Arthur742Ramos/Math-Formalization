/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile12Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (130089/131072 : ℚ), (-3369977987537717914546714999)⟩

theorem profile12Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join01_0011Claim :=
  profile12Join00_0022Bound.glue profile12Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
