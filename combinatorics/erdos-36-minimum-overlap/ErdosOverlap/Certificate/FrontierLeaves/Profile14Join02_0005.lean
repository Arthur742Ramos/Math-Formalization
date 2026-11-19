/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile14Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (16269/16384 : ℚ), (-3161844382544056432916158350)⟩

theorem profile14Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join02_0005Claim :=
  profile14Join01_0010Bound.glue profile14Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
