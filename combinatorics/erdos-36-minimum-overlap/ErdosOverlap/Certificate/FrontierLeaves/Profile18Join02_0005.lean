/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (16263/16384 : ℚ), (-3282415963184493672586785615)⟩

theorem profile18Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join02_0005Claim :=
  profile18Join01_0010Bound.glue profile18Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
