/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin02_0005Claim : IntegralClaim := ⟨(9283/16384 : ℚ), (40973/60416 : ℚ), 142807949246848134473172762608953637693⟩

theorem denominatorJoin02_0005Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0005Claim :=
  denominatorJoin01_0010Bound.glue denominatorJoin01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
