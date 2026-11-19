/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0008
public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorBlock0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def denominatorJoin00_0004Claim : IntegralClaim := ⟨(991/131072 : ℚ), (1247/131072 : ℚ), 1505041989964931172061522020989⟩

theorem denominatorJoin00_0004Bound : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorJoin00_0004Claim :=
  denominatorBlock0008.glue denominatorBlock0009 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
