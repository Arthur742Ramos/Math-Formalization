/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0002
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0001Claim : IntegralClaim := ⟨(223/131072 : ℚ), (479/131072 : ℚ), 2241422601799033300155021823728⟩

theorem denominatorJoin00_0001Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0001Claim :=
  denominatorBlock0002.glue denominatorBlock0003 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
