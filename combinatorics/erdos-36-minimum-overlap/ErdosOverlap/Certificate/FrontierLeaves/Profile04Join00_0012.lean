/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join00_0012Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (8021/16384 : ℚ), 6514659457531822322536597487114⟩

theorem profile04Join00_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0012Claim :=
  profile04Block0024.glue profile04Block0025 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
