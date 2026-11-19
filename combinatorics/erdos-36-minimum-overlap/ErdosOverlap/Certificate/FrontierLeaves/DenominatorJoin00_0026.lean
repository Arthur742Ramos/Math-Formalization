/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0052
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0053

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0026Claim : IntegralClaim := ⟨(12339/16384 : ℚ), (556003/704512 : ℚ), 18713780891399627688814308631655283549⟩

theorem denominatorJoin00_0026Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0026Claim :=
  denominatorBlock0052.glue denominatorBlock0053 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
