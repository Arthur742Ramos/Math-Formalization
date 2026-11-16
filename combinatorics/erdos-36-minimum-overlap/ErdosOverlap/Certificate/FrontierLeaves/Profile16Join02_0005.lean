/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile16Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (260195/262144 : ℚ), (-3402743318281043199167664261)⟩

theorem profile16Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join02_0005Claim :=
  profile16Join01_0010Bound.glue profile16Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
