/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join00_0003Claim : IntegralClaim := ⟨(1871/262144 : ℚ), (319/32768 : ℚ), 0⟩

theorem profile04Join00_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0003Claim :=
  profile04Block0006.glue profile04Block0007 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
