/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0010
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0005Claim : IntegralClaim := ⟨(5349/262144 : ℚ), (51257/2097152 : ℚ), 3694934794825949384870033477528⟩

theorem denominatorJoin01_0005Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0005Claim :=
  denominatorJoin00_0010Bound.glue denominatorJoin00_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
