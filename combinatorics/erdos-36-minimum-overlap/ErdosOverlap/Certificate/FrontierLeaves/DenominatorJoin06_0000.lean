/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0032
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin05_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin06_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 894002570503891078545761945071152344239⟩

theorem denominatorJoin06_0000Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin06_0000Claim :=
  denominatorJoin05_0000Bound.glue denominatorJoin00_0032Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
