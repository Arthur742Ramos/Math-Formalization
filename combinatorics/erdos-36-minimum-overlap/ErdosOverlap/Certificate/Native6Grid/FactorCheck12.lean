module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6TrigData
public import ErdosOverlap.Certificate.Native6Grid.Factors03

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorCheck12 : factorRowCheck Native6Trig.terms 12 factors12 = true := by
  decide +kernel

theorem factors12_correct : FactorRowCorrect Native6Trig.terms 12 factors12 :=
  factorRowCheck_sound factorCheck12

end
end ErdosOverlap.Native6Grid
