/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck016
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck017
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck018
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck019
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck020
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck021
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck022
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck023

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk002 (j : ℕ) (hlo : 128 ≤ j) (hhi : j < 192) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0128
  · exact transition0129
  · exact transition0130
  · exact transition0131
  · exact transition0132
  · exact transition0133
  · exact transition0134
  · exact transition0135
  · exact transition0136
  · exact transition0137
  · exact transition0138
  · exact transition0139
  · exact transition0140
  · exact transition0141
  · exact transition0142
  · exact transition0143
  · exact transition0144
  · exact transition0145
  · exact transition0146
  · exact transition0147
  · exact transition0148
  · exact transition0149
  · exact transition0150
  · exact transition0151
  · exact transition0152
  · exact transition0153
  · exact transition0154
  · exact transition0155
  · exact transition0156
  · exact transition0157
  · exact transition0158
  · exact transition0159
  · exact transition0160
  · exact transition0161
  · exact transition0162
  · exact transition0163
  · exact transition0164
  · exact transition0165
  · exact transition0166
  · exact transition0167
  · exact transition0168
  · exact transition0169
  · exact transition0170
  · exact transition0171
  · exact transition0172
  · exact transition0173
  · exact transition0174
  · exact transition0175
  · exact transition0176
  · exact transition0177
  · exact transition0178
  · exact transition0179
  · exact transition0180
  · exact transition0181
  · exact transition0182
  · exact transition0183
  · exact transition0184
  · exact transition0185
  · exact transition0186
  · exact transition0187
  · exact transition0188
  · exact transition0189
  · exact transition0190
  · exact transition0191

end
end ErdosOverlap.Native6Grid
