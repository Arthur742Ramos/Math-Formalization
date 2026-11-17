/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0020
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0021

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile10Join00_0010Claim : IntegralClaim := ⟨(7685/262144 : ℚ), (327871/1048576 : ℚ), 7357949903630429332384032589753⟩

theorem profile10Join00_0010Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join00_0010Claim :=
  profile10Block0020.glue profile10Block0021 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
