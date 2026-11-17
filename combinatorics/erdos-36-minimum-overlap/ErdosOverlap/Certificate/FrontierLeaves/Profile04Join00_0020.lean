/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0040
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0041

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join00_0020Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (891/1024 : ℚ), 0⟩

theorem profile04Join00_0020Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0020Claim :=
  profile04Block0040.glue profile04Block0041 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
