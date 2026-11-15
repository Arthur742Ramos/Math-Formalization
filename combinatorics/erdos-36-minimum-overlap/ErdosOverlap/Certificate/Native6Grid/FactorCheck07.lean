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

theorem factorCheck07 : factorRowCheck Native6Trig.terms 7 factors07 = true := by
  decide +kernel

theorem factors07_correct : FactorRowCorrect Native6Trig.terms 7 factors07 :=
  factorRowCheck_sound factorCheck07

end
end ErdosOverlap.Native6Grid
