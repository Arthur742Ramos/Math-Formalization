/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0026
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0027

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0013Claim : IntegralClaim := ⟨(116787/4194304 : ℚ), (83/512 : ℚ), 37078472316303817653768133121891678205⟩

theorem denominatorJoin00_0013Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0013Claim :=
  denominatorBlock0026.glue denominatorBlock0027 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
