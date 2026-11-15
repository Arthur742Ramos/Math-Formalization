/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck008
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck009
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck010
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck011
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck012
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck013
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck014
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck015

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk001 (j : ℕ) (hlo : 64 ≤ j) (hhi : j < 128) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0064
  · exact transition0065
  · exact transition0066
  · exact transition0067
  · exact transition0068
  · exact transition0069
  · exact transition0070
  · exact transition0071
  · exact transition0072
  · exact transition0073
  · exact transition0074
  · exact transition0075
  · exact transition0076
  · exact transition0077
  · exact transition0078
  · exact transition0079
  · exact transition0080
  · exact transition0081
  · exact transition0082
  · exact transition0083
  · exact transition0084
  · exact transition0085
  · exact transition0086
  · exact transition0087
  · exact transition0088
  · exact transition0089
  · exact transition0090
  · exact transition0091
  · exact transition0092
  · exact transition0093
  · exact transition0094
  · exact transition0095
  · exact transition0096
  · exact transition0097
  · exact transition0098
  · exact transition0099
  · exact transition0100
  · exact transition0101
  · exact transition0102
  · exact transition0103
  · exact transition0104
  · exact transition0105
  · exact transition0106
  · exact transition0107
  · exact transition0108
  · exact transition0109
  · exact transition0110
  · exact transition0111
  · exact transition0112
  · exact transition0113
  · exact transition0114
  · exact transition0115
  · exact transition0116
  · exact transition0117
  · exact transition0118
  · exact transition0119
  · exact transition0120
  · exact transition0121
  · exact transition0122
  · exact transition0123
  · exact transition0124
  · exact transition0125
  · exact transition0126
  · exact transition0127

end
end ErdosOverlap.Native6Grid
