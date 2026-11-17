/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0042
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0043

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0021Claim : IntegralClaim := ⟨(5119191/8323072 : ℚ), (42757/65536 : ℚ), 45853537307944565681038235114079859039⟩

theorem denominatorJoin00_0021Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0021Claim :=
  denominatorBlock0042.glue denominatorBlock0043 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
