/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0060
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0061

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0030Claim : IntegralClaim := ⟨(1868035/2097152 : ℚ), (1278477/1359872 : ℚ), 3165331040687641243303234638205570724⟩

theorem denominatorJoin00_0030Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0030Claim :=
  denominatorBlock0060.glue denominatorBlock0061 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
