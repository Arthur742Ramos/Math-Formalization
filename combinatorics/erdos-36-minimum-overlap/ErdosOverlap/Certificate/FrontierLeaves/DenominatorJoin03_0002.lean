/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin03_0002Claim : IntegralClaim := ⟨(104735/262144 : ℚ), (40973/60416 : ℚ), 434805547067627498963883083024341767342⟩

theorem denominatorJoin03_0002Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0002Claim :=
  denominatorJoin02_0004Bound.glue denominatorJoin02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
