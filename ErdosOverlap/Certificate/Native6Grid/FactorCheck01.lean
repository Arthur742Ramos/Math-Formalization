module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6TrigData
public import ErdosOverlap.Certificate.Native6Grid.Factors00

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorCheck01 : factorRowCheck Native6Trig.terms 1 factors01 = true := by
  decide +kernel

theorem factors01_correct : FactorRowCorrect Native6Trig.terms 1 factors01 :=
  factorRowCheck_sound factorCheck01

end
end ErdosOverlap.Native6Grid
