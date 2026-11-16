/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0016
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorJoin00_0008Claim : IntegralClaim := ⟨(64435/4194304 : ℚ), (18349/1048576 : ℚ), 6153706230329766061500741372240⟩

theorem denominatorJoin00_0008Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0008Claim :=
  denominatorBlock0016.glue denominatorBlock0017 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
