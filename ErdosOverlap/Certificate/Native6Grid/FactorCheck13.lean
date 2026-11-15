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

theorem factorCheck13 : factorRowCheck Native6Trig.terms 13 factors13 = true := by
  decide +kernel

theorem factors13_correct : FactorRowCorrect Native6Trig.terms 13 factors13 :=
  factorRowCheck_sound factorCheck13

end
end ErdosOverlap.Native6Grid
