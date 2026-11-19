/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join01_0012Claim : IntegralClaim := ⟨(127357/131072 : ℚ), (129005/131072 : ℚ), (-6761174168857186591911152116673)⟩

theorem profile08Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join01_0012Claim :=
  profile08Join00_0024Bound.glue profile08Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
