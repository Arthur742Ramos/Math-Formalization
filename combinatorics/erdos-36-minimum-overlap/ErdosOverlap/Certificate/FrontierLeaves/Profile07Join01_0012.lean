/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join01_0012Claim : IntegralClaim := ⟨(63943/65536 : ℚ), (129413/131072 : ℚ), (-5792645799082225413330520781569)⟩

theorem profile07Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join01_0012Claim :=
  profile07Join00_0024Bound.glue profile07Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
