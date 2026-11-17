/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0018
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin01_0009Claim : IntegralClaim := ⟨(65487/131072 : ℚ), (9283/16384 : ℚ), 111303957204986195331220637985863398363⟩

theorem denominatorJoin01_0009Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0009Claim :=
  denominatorJoin00_0018Bound.glue denominatorJoin00_0019Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
