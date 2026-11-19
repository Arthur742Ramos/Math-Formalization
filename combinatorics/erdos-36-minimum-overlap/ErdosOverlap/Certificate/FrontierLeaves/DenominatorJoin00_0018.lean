/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0036
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0037

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0018Claim : IntegralClaim := ⟨(65487/131072 : ℚ), (2101/4096 : ℚ), 23215804812167101159396132862866349527⟩

theorem denominatorJoin00_0018Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0018Claim :=
  denominatorBlock0036.glue denominatorBlock0037 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
