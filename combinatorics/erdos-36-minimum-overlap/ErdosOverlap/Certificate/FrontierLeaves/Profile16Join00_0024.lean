/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile16Join00_0024Claim : IntegralClaim := ⟨(260195/262144 : ℚ), (1/1 : ℚ), (-3863626323627781001519594417)⟩

theorem profile16Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join00_0024Claim :=
  profile16Block0048.glue profile16Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
