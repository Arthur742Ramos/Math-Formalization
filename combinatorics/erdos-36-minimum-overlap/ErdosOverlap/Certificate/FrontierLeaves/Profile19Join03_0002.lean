/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile19Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (16265/16384 : ℚ), 991656110371195223849483322162⟩

theorem profile19Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join03_0002Claim :=
  profile19Join02_0004Bound.glue profile19Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
