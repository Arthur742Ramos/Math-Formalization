/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0058
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0059

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0029Claim : IntegralClaim := ⟨(3603941/4194304 : ℚ), (1868035/2097152 : ℚ), 4596913610221859743498819769250236322⟩

theorem denominatorJoin00_0029Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0029Claim :=
  denominatorBlock0058.glue denominatorBlock0059 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
