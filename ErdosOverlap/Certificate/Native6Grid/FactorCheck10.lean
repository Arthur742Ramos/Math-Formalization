module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Certificate.Native6TrigData
public import ErdosOverlap.Certificate.Native6Grid.Factors02

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorCheck10 : factorRowCheck Native6Trig.terms 10 factors10 = true := by
  decide +kernel

theorem factors10_correct : FactorRowCorrect Native6Trig.terms 10 factors10 :=
  factorRowCheck_sound factorCheck10

end
end ErdosOverlap.Native6Grid
