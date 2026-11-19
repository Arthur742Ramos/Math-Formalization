/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0012
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin02_0006Claim : IntegralClaim := ⟨(40973/60416 : ℚ), (3502137/4194304 : ℚ), 94079176570523035321003832358902307427⟩

theorem denominatorJoin02_0006Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0006Claim :=
  denominatorJoin01_0012Bound.glue denominatorJoin01_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
