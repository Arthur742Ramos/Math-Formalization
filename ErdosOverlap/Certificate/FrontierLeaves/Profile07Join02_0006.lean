/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join01_0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join01_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join02_0006Claim : IntegralClaim := ⟨(63943/65536 : ℚ), (1/1 : ℚ), (-9408297000666497019075184302500)⟩

theorem profile07Join02_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join02_0006Claim :=
  profile07Join01_0012Bound.glue profile07Join01_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
