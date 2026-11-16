/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join00_0023Claim : IntegralClaim := ⟨(126885/131072 : ℚ), (63943/65536 : ℚ), (-3790975405701377080999535000145)⟩

theorem profile07Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0023Claim :=
  profile07Block0046.glue profile07Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
