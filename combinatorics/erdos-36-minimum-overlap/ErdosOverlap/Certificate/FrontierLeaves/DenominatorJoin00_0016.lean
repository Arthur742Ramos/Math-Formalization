/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0032
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0033

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0016Claim : IntegralClaim := ⟨(104735/262144 : ℚ), (118663/262144 : ℚ), 96320563393464841360510378574409042694⟩

theorem denominatorJoin00_0016Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0016Claim :=
  denominatorBlock0032.glue denominatorBlock0033 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
