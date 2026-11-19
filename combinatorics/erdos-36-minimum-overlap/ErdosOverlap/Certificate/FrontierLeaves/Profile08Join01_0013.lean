/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0026
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join01_0013Claim : IntegralClaim := ⟨(129005/131072 : ℚ), (1/1 : ℚ), (-5104237631982862483441625202822)⟩

theorem profile08Join01_0013Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join01_0013Claim :=
  profile08Join00_0026Bound.glue profile08Join00_0027Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
