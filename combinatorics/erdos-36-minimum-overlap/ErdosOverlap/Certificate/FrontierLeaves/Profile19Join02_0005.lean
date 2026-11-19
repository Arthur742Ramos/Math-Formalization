/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile19Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (16265/16384 : ℚ), (-3158130968766795795794174846)⟩

theorem profile19Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join02_0005Claim :=
  profile19Join01_0010Bound.glue profile19Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
