/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0026
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin00_0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin01_0013Claim : IntegralClaim := ⟨(12339/16384 : ℚ), (3502137/4194304 : ℚ), 34644570035107453288135027700681099740⟩

theorem denominatorJoin01_0013Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin01_0013Claim :=
  denominatorJoin00_0026Bound.glue denominatorJoin00_0027Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
