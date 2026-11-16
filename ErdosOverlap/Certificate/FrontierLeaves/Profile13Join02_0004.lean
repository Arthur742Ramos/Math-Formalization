/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join01_0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join01_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join02_0004Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (54239/65536 : ℚ), 994814241339962019645277497008⟩

theorem profile13Join02_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join02_0004Claim :=
  profile13Join01_0008Bound.glue profile13Join01_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
