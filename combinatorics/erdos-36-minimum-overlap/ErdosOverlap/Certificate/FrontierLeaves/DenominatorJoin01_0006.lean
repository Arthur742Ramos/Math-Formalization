/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0012
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0006Claim : IntegralClaim := ⟨(51257/2097152 : ℚ), (83/512 : ℚ), 37078491954385090169495591788970730892⟩

theorem denominatorJoin01_0006Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0006Claim :=
  denominatorJoin00_0012Bound.glue denominatorJoin00_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
