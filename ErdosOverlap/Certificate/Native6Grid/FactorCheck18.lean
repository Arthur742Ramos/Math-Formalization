module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6TrigData
public import ErdosOverlap.Certificate.Native6Grid.Factors04

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorCheck18 : factorRowCheck Native6Trig.terms 18 factors18 = true := by
  decide +kernel

theorem factors18_correct : FactorRowCorrect Native6Trig.terms 18 factors18 :=
  factorRowCheck_sound factorCheck18

end
end ErdosOverlap.Native6Grid
