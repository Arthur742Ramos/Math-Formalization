/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join02_0006Claim : IntegralClaim := ⟨(127357/131072 : ℚ), (1/1 : ℚ), (-11865411800840049075352777319495)⟩

theorem profile08Join02_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join02_0006Claim :=
  profile08Join01_0012Bound.glue profile08Join01_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
