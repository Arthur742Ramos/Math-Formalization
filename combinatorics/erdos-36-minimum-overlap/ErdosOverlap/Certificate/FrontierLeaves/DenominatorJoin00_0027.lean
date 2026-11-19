/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0054
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0055

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0027Claim : IntegralClaim := ⟨(556003/704512 : ℚ), (3502137/4194304 : ℚ), 15930789143707825599320719069025816191⟩

theorem denominatorJoin00_0027Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0027Claim :=
  denominatorBlock0054.glue denominatorBlock0055 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
