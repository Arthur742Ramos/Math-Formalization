/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile18Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (16263/16384 : ℚ), (-3282415963184493672586785615)⟩

theorem profile18Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0023Claim :=
  profile18Block0046.glue profile18Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
