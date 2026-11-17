/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0014
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0007Claim : IntegralClaim := ⟨(1759/131072 : ℚ), (64435/4194304 : ℚ), 5521466996190806737585063195149⟩

theorem denominatorJoin00_0007Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0007Claim :=
  denominatorBlock0014.glue denominatorBlock0015 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
