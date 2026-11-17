/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0030
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0031

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0015Claim : IntegralClaim := ⟨(24571/72704 : ℚ), (104735/262144 : ℚ), 105798480467045865054341399219234656707⟩

theorem denominatorJoin00_0015Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0015Claim :=
  denominatorBlock0030.glue denominatorBlock0031 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
