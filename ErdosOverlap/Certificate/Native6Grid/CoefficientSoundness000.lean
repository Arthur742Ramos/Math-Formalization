/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck000
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck001
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck002
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck003
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck004
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck005
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck006
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck007

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk000 (j : ℕ) (hlo : 0 ≤ j) (hhi : j < 64) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0000
  · exact coefficientCheck0001
  · exact coefficientCheck0002
  · exact coefficientCheck0003
  · exact coefficientCheck0004
  · exact coefficientCheck0005
  · exact coefficientCheck0006
  · exact coefficientCheck0007
  · exact coefficientCheck0008
  · exact coefficientCheck0009
  · exact coefficientCheck0010
  · exact coefficientCheck0011
  · exact coefficientCheck0012
  · exact coefficientCheck0013
  · exact coefficientCheck0014
  · exact coefficientCheck0015
  · exact coefficientCheck0016
  · exact coefficientCheck0017
  · exact coefficientCheck0018
  · exact coefficientCheck0019
  · exact coefficientCheck0020
  · exact coefficientCheck0021
  · exact coefficientCheck0022
  · exact coefficientCheck0023
  · exact coefficientCheck0024
  · exact coefficientCheck0025
  · exact coefficientCheck0026
  · exact coefficientCheck0027
  · exact coefficientCheck0028
  · exact coefficientCheck0029
  · exact coefficientCheck0030
  · exact coefficientCheck0031
  · exact coefficientCheck0032
  · exact coefficientCheck0033
  · exact coefficientCheck0034
  · exact coefficientCheck0035
  · exact coefficientCheck0036
  · exact coefficientCheck0037
  · exact coefficientCheck0038
  · exact coefficientCheck0039
  · exact coefficientCheck0040
  · exact coefficientCheck0041
  · exact coefficientCheck0042
  · exact coefficientCheck0043
  · exact coefficientCheck0044
  · exact coefficientCheck0045
  · exact coefficientCheck0046
  · exact coefficientCheck0047
  · exact coefficientCheck0048
  · exact coefficientCheck0049
  · exact coefficientCheck0050
  · exact coefficientCheck0051
  · exact coefficientCheck0052
  · exact coefficientCheck0053
  · exact coefficientCheck0054
  · exact coefficientCheck0055
  · exact coefficientCheck0056
  · exact coefficientCheck0057
  · exact coefficientCheck0058
  · exact coefficientCheck0059
  · exact coefficientCheck0060
  · exact coefficientCheck0061
  · exact coefficientCheck0062
  · exact coefficientCheck0063

end
end ErdosOverlap.Native6Grid
