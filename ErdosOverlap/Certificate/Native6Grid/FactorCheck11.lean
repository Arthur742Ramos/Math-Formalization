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

theorem factorCheck11 : factorRowCheck Native6Trig.terms 11 factors11 = true := by
  decide +kernel

theorem factors11_correct : FactorRowCorrect Native6Trig.terms 11 factors11 :=
  factorRowCheck_sound factorCheck11

end
end ErdosOverlap.Native6Grid
