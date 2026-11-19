/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0022
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0011Claim : IntegralClaim := ⟨(2851/131072 : ℚ), (51257/2097152 : ℚ), 3207377612065799403108920147601⟩

theorem denominatorJoin00_0011Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0011Claim :=
  denominatorBlock0022.glue denominatorBlock0023 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
