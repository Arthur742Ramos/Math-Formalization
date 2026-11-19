/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile10Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (4059/4096 : ℚ), (-3201208064343582036509040950)⟩

theorem profile10Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join02_0005Claim :=
  profile10Join01_0010Bound.glue profile10Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
