/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0011Claim : IntegralClaim := ⟨(42757/65536 : ℚ), (40973/60416 : ℚ), 27353600334161743522505713978736521881⟩

theorem denominatorJoin01_0011Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0011Claim :=
  denominatorJoin00_0022Bound.glue denominatorJoin00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
