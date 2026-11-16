/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0004
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0002Claim : IntegralClaim := ⟨(991/131072 : ℚ), (1503/131072 : ℚ), 2915826641716395217649754961768⟩

theorem denominatorJoin01_0002Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0002Claim :=
  denominatorJoin00_0004Bound.glue denominatorJoin00_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
