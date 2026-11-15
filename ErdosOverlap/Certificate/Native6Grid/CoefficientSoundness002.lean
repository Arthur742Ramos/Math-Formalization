/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck016
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck017
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck018
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck019
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck020
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck021
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck022
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck023

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk002 (j : ℕ) (hlo : 128 ≤ j) (hhi : j < 192) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0128
  · exact coefficientCheck0129
  · exact coefficientCheck0130
  · exact coefficientCheck0131
  · exact coefficientCheck0132
  · exact coefficientCheck0133
  · exact coefficientCheck0134
  · exact coefficientCheck0135
  · exact coefficientCheck0136
  · exact coefficientCheck0137
  · exact coefficientCheck0138
  · exact coefficientCheck0139
  · exact coefficientCheck0140
  · exact coefficientCheck0141
  · exact coefficientCheck0142
  · exact coefficientCheck0143
  · exact coefficientCheck0144
  · exact coefficientCheck0145
  · exact coefficientCheck0146
  · exact coefficientCheck0147
  · exact coefficientCheck0148
  · exact coefficientCheck0149
  · exact coefficientCheck0150
  · exact coefficientCheck0151
  · exact coefficientCheck0152
  · exact coefficientCheck0153
  · exact coefficientCheck0154
  · exact coefficientCheck0155
  · exact coefficientCheck0156
  · exact coefficientCheck0157
  · exact coefficientCheck0158
  · exact coefficientCheck0159
  · exact coefficientCheck0160
  · exact coefficientCheck0161
  · exact coefficientCheck0162
  · exact coefficientCheck0163
  · exact coefficientCheck0164
  · exact coefficientCheck0165
  · exact coefficientCheck0166
  · exact coefficientCheck0167
  · exact coefficientCheck0168
  · exact coefficientCheck0169
  · exact coefficientCheck0170
  · exact coefficientCheck0171
  · exact coefficientCheck0172
  · exact coefficientCheck0173
  · exact coefficientCheck0174
  · exact coefficientCheck0175
  · exact coefficientCheck0176
  · exact coefficientCheck0177
  · exact coefficientCheck0178
  · exact coefficientCheck0179
  · exact coefficientCheck0180
  · exact coefficientCheck0181
  · exact coefficientCheck0182
  · exact coefficientCheck0183
  · exact coefficientCheck0184
  · exact coefficientCheck0185
  · exact coefficientCheck0186
  · exact coefficientCheck0187
  · exact coefficientCheck0188
  · exact coefficientCheck0189
  · exact coefficientCheck0190
  · exact coefficientCheck0191

end
end ErdosOverlap.Native6Grid
