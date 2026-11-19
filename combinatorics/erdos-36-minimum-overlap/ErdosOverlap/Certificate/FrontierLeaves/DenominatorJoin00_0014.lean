/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0028
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0029

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0014Claim : IntegralClaim := ⟨(83/512 : ℚ), (24571/72704 : ℚ), 208437103352471650885684304203818621817⟩

theorem denominatorJoin00_0014Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0014Claim :=
  denominatorBlock0028.glue denominatorBlock0029 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
