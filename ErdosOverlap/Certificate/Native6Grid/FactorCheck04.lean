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

theorem factorCheck04 : factorRowCheck Native6Trig.terms 4 factors04 = true := by
  decide +kernel

theorem factors04_correct : FactorRowCorrect Native6Trig.terms 4 factors04 :=
  factorRowCheck_sound factorCheck04

end
end ErdosOverlap.Native6Grid
