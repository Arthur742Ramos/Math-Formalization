/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0008
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0004Claim : IntegralClaim := ⟨(64435/4194304 : ℚ), (5349/262144 : ℚ), 9056252942408007823712836381821⟩

theorem denominatorJoin01_0004Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0004Claim :=
  denominatorJoin00_0008Bound.glue denominatorJoin00_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
