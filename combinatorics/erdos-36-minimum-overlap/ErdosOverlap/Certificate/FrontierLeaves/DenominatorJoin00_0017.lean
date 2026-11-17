/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0034
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0035

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0017Claim : IntegralClaim := ⟨(118663/262144 : ℚ), (65487/131072 : ℚ), 84373077222328327798979303855115688592⟩

theorem denominatorJoin00_0017Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0017Claim :=
  denominatorBlock0034.glue denominatorBlock0035 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
