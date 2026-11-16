module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6TrigData
public import ErdosOverlap.Certificate.Native6Grid.Factors01

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorCheck06 : factorRowCheck Native6Trig.terms 6 factors06 = true := by
  decide +kernel

theorem factors06_correct : FactorRowCorrect Native6Trig.terms 6 factors06 :=
  factorRowCheck_sound factorCheck06

end
end ErdosOverlap.Native6Grid
