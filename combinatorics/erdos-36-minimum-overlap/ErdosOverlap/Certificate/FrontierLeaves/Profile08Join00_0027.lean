/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0054
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0055

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join00_0027Claim : IntegralClaim := ⟨(259609/262144 : ℚ), (1/1 : ℚ), (-2154444542686380602863525556187)⟩

theorem profile08Join00_0027Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0027Claim :=
  profile08Block0054.glue profile08Block0055 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
