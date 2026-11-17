/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0062
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0063

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0031Claim : IntegralClaim := ⟨(1278477/1359872 : ℚ), (127673/131072 : ℚ), 540556292190462388992262349759413734⟩

theorem denominatorJoin00_0031Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0031Claim :=
  denominatorBlock0062.glue denominatorBlock0063 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
