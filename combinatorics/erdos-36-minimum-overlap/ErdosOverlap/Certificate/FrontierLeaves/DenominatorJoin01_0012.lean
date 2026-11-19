/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0012Claim : IntegralClaim := ⟨(40973/60416 : ℚ), (12339/16384 : ℚ), 59434606535415582032868804658221207687⟩

theorem denominatorJoin01_0012Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0012Claim :=
  denominatorJoin00_0024Bound.glue denominatorJoin00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
