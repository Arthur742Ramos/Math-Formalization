/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (130089/131072 : ℚ), (-3369977987537717914546714999)⟩

theorem profile12Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join02_0005Claim :=
  profile12Join01_0010Bound.glue profile12Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
