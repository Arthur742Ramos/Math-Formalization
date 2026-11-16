/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (130101/131072 : ℚ), 991470843912809874260644624977⟩

theorem profile17Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join03_0002Claim :=
  profile17Join02_0004Bound.glue profile17Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
