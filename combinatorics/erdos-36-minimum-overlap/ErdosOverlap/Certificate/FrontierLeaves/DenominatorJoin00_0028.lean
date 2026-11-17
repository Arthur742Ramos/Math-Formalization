/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0056
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0057

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0028Claim : IntegralClaim := ⟨(3502137/4194304 : ℚ), (3603941/4194304 : ℚ), 5447136861405178265202626349633116749⟩

theorem denominatorJoin00_0028Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0028Claim :=
  denominatorBlock0056.glue denominatorBlock0057 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
