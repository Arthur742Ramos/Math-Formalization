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

theorem factorCheck02 : factorRowCheck Native6Trig.terms 2 factors02 = true := by
  decide +kernel

theorem factors02_correct : FactorRowCorrect Native6Trig.terms 2 factors02 :=
  factorRowCheck_sound factorCheck02

end
end ErdosOverlap.Native6Grid
