/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0008
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin01_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin02_0004Claim : IntegralClaim := ⟨(104735/262144 : ℚ), (9283/16384 : ℚ), 291997597820779364490710320415388129649⟩

theorem denominatorJoin02_0004Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin02_0004Claim :=
  denominatorJoin01_0008Bound.glue denominatorJoin01_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
