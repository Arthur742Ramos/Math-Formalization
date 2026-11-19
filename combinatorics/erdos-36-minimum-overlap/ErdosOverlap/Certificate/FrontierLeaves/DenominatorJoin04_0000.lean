/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin03_0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin03_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin04_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (104735/262144 : ℚ), 351314105318420025199396222179188307017⟩

theorem denominatorJoin04_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin04_0000Claim :=
  denominatorJoin03_0000Bound.glue denominatorJoin03_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
