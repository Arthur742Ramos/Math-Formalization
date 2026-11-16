/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck008
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck009
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck010
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck011
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck012
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck013
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck014
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck015

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk001 (j : ℕ) (hlo : 64 ≤ j) (hhi : j < 128) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0064
  · exact coefficientCheck0065
  · exact coefficientCheck0066
  · exact coefficientCheck0067
  · exact coefficientCheck0068
  · exact coefficientCheck0069
  · exact coefficientCheck0070
  · exact coefficientCheck0071
  · exact coefficientCheck0072
  · exact coefficientCheck0073
  · exact coefficientCheck0074
  · exact coefficientCheck0075
  · exact coefficientCheck0076
  · exact coefficientCheck0077
  · exact coefficientCheck0078
  · exact coefficientCheck0079
  · exact coefficientCheck0080
  · exact coefficientCheck0081
  · exact coefficientCheck0082
  · exact coefficientCheck0083
  · exact coefficientCheck0084
  · exact coefficientCheck0085
  · exact coefficientCheck0086
  · exact coefficientCheck0087
  · exact coefficientCheck0088
  · exact coefficientCheck0089
  · exact coefficientCheck0090
  · exact coefficientCheck0091
  · exact coefficientCheck0092
  · exact coefficientCheck0093
  · exact coefficientCheck0094
  · exact coefficientCheck0095
  · exact coefficientCheck0096
  · exact coefficientCheck0097
  · exact coefficientCheck0098
  · exact coefficientCheck0099
  · exact coefficientCheck0100
  · exact coefficientCheck0101
  · exact coefficientCheck0102
  · exact coefficientCheck0103
  · exact coefficientCheck0104
  · exact coefficientCheck0105
  · exact coefficientCheck0106
  · exact coefficientCheck0107
  · exact coefficientCheck0108
  · exact coefficientCheck0109
  · exact coefficientCheck0110
  · exact coefficientCheck0111
  · exact coefficientCheck0112
  · exact coefficientCheck0113
  · exact coefficientCheck0114
  · exact coefficientCheck0115
  · exact coefficientCheck0116
  · exact coefficientCheck0117
  · exact coefficientCheck0118
  · exact coefficientCheck0119
  · exact coefficientCheck0120
  · exact coefficientCheck0121
  · exact coefficientCheck0122
  · exact coefficientCheck0123
  · exact coefficientCheck0124
  · exact coefficientCheck0125
  · exact coefficientCheck0126
  · exact coefficientCheck0127

end
end ErdosOverlap.Native6Grid
