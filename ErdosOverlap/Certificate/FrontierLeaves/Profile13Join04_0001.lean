/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join01_0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile13Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), 977999472463229635938864841097⟩

theorem profile13Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join04_0001Claim :=
  profile13Join03_0002Bound.glue profile13Join01_0012Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
