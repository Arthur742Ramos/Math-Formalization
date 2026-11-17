/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0030
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0031

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile14Join00_0015Claim : IntegralClaim := ⟨(77107/131072 : ℚ), (9289/14276 : ℚ), 817830468686537408978815160415⟩

theorem profile14Join00_0015Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0015Claim :=
  profile14Block0030.glue profile14Block0031 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
