/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0012
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0006Claim : IntegralClaim := ⟨(1503/131072 : ℚ), (1759/131072 : ℚ), 1420125111596636306161033167864⟩

theorem denominatorJoin00_0006Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0006Claim :=
  denominatorBlock0012.glue denominatorBlock0013 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
