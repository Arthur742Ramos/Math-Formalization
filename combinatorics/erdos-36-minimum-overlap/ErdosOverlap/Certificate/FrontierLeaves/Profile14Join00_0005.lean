/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile14Join00_0005Claim : IntegralClaim := ⟨(12941/1048576 : ℚ), (15667/1048576 : ℚ), 0⟩

theorem profile14Join00_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0005Claim :=
  profile14Block0010.glue profile14Block0011 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
