/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck024
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck025
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck026
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck027
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck028
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck029
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck030
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck031

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk003 (j : ℕ) (hlo : 192 ≤ j) (hhi : j < 256) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0192
  · exact coefficientCheck0193
  · exact coefficientCheck0194
  · exact coefficientCheck0195
  · exact coefficientCheck0196
  · exact coefficientCheck0197
  · exact coefficientCheck0198
  · exact coefficientCheck0199
  · exact coefficientCheck0200
  · exact coefficientCheck0201
  · exact coefficientCheck0202
  · exact coefficientCheck0203
  · exact coefficientCheck0204
  · exact coefficientCheck0205
  · exact coefficientCheck0206
  · exact coefficientCheck0207
  · exact coefficientCheck0208
  · exact coefficientCheck0209
  · exact coefficientCheck0210
  · exact coefficientCheck0211
  · exact coefficientCheck0212
  · exact coefficientCheck0213
  · exact coefficientCheck0214
  · exact coefficientCheck0215
  · exact coefficientCheck0216
  · exact coefficientCheck0217
  · exact coefficientCheck0218
  · exact coefficientCheck0219
  · exact coefficientCheck0220
  · exact coefficientCheck0221
  · exact coefficientCheck0222
  · exact coefficientCheck0223
  · exact coefficientCheck0224
  · exact coefficientCheck0225
  · exact coefficientCheck0226
  · exact coefficientCheck0227
  · exact coefficientCheck0228
  · exact coefficientCheck0229
  · exact coefficientCheck0230
  · exact coefficientCheck0231
  · exact coefficientCheck0232
  · exact coefficientCheck0233
  · exact coefficientCheck0234
  · exact coefficientCheck0235
  · exact coefficientCheck0236
  · exact coefficientCheck0237
  · exact coefficientCheck0238
  · exact coefficientCheck0239
  · exact coefficientCheck0240
  · exact coefficientCheck0241
  · exact coefficientCheck0242
  · exact coefficientCheck0243
  · exact coefficientCheck0244
  · exact coefficientCheck0245
  · exact coefficientCheck0246
  · exact coefficientCheck0247
  · exact coefficientCheck0248
  · exact coefficientCheck0249
  · exact coefficientCheck0250
  · exact coefficientCheck0251
  · exact coefficientCheck0252
  · exact coefficientCheck0253
  · exact coefficientCheck0254
  · exact coefficientCheck0255

end
end ErdosOverlap.Native6Grid
