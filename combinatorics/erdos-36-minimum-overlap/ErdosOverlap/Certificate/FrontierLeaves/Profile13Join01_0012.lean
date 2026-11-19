/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join00_0024

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile13Join01_0012Claim : IntegralClaim := ⟨(1034617/1048576 : ℚ), (1/1 : ℚ), (-13616190321468974375712405714)⟩

theorem profile13Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join01_0012Claim :=
  profile13Join00_0024Bound.glue profile13Block0050 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
