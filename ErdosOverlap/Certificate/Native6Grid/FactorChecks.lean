module

public import ErdosOverlap.Certificate.Native6Grid.FactorRows
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck00
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck01
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck02
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck03
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck04
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck05
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck06
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck07
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck08
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck09
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck10
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck11
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck12
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck13
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck14
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck15
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck16
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck17
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck18
public import ErdosOverlap.Certificate.Native6Grid.FactorCheck19

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem factorRows_correct (k : ℕ) (hk : k < 20) :
    FactorRowCorrect Native6Trig.terms k (factorRow k) := by
  interval_cases k
  · exact factors00_correct
  · exact factors01_correct
  · exact factors02_correct
  · exact factors03_correct
  · exact factors04_correct
  · exact factors05_correct
  · exact factors06_correct
  · exact factors07_correct
  · exact factors08_correct
  · exact factors09_correct
  · exact factors10_correct
  · exact factors11_correct
  · exact factors12_correct
  · exact factors13_correct
  · exact factors14_correct
  · exact factors15_correct
  · exact factors16_correct
  · exact factors17_correct
  · exact factors18_correct
  · exact factors19_correct

end
end ErdosOverlap.Native6Grid
