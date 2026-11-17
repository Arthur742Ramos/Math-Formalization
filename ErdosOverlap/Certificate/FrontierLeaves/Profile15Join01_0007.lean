/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join00_0014
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join00_0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile15Join01_0007Claim : IntegralClaim := ⟨(1633327/3178496 : ℚ), (9289/14276 : ℚ), 2632152158876669267512200913384⟩

theorem profile15Join01_0007Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join01_0007Claim :=
  profile15Join00_0014Bound.glue profile15Join00_0015Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
