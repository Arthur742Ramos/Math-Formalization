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

theorem factorCheck09 : factorRowCheck Native6Trig.terms 9 factors09 = true := by
  decide +kernel

theorem factors09_correct : FactorRowCorrect Native6Trig.terms 9 factors09 :=
  factorRowCheck_sound factorCheck09

end
end ErdosOverlap.Native6Grid
