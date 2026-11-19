/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0014
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join01_0007Claim : IntegralClaim := ⟨(1633327/3178496 : ℚ), (9289/14276 : ℚ), 2632152158876669267512200913384⟩

theorem profile09Join01_0007Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join01_0007Claim :=
  profile09Join00_0014Bound.glue profile09Join00_0015Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
