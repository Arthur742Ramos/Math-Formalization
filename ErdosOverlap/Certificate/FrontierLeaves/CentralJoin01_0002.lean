/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0004
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin01_0002Claim : IntegralClaim := ⟨(106311/241664 : ℚ), (2879/5080 : ℚ), 7590109787457706567104034388614⟩

theorem centralJoin01_0002Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0002Claim :=
  centralJoin00_0004Bound.glue centralJoin00_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
