/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0000
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin02_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin03_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (64435/4194304 : ℚ), 16793329681855917718384294438252⟩

theorem denominatorJoin03_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin03_0000Claim :=
  denominatorJoin02_0000Bound.glue denominatorJoin02_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
