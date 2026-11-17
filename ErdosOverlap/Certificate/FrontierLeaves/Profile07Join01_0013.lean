/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0054
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join00_0026

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join01_0013Claim : IntegralClaim := ⟨(129413/131072 : ℚ), (1/1 : ℚ), (-3615651201584271605744663520931)⟩

theorem profile07Join01_0013Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join01_0013Claim :=
  profile07Join00_0026Bound.glue profile07Block0054 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
