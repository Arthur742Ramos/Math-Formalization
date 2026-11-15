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

theorem factorCheck15 : factorRowCheck Native6Trig.terms 15 factors15 = true := by
  decide +kernel

theorem factors15_correct : FactorRowCorrect Native6Trig.terms 15 factors15 :=
  factorRowCheck_sound factorCheck15

end
end ErdosOverlap.Native6Grid
