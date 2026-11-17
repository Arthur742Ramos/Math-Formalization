/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0006
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0003Claim : IntegralClaim := ⟨(735/131072 : ℚ), (991/131072 : ℚ), 1479540062444542157251024199341⟩

theorem denominatorJoin00_0003Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0003Claim :=
  denominatorBlock0006.glue denominatorBlock0007 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
