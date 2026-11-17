/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0014
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0015

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0007Claim : IntegralClaim := ⟨(83/512 : ℚ), (104735/262144 : ℚ), 314235583819517515940025703423053278524⟩

theorem denominatorJoin01_0007Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0007Claim :=
  denominatorJoin00_0014Bound.glue denominatorJoin00_0015Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
