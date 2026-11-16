/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck024
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck025
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck026
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck027
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck028
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck029
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck030
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck031

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk003 (j : ℕ) (hlo : 192 ≤ j) (hhi : j < 256) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0192
  · exact transition0193
  · exact transition0194
  · exact transition0195
  · exact transition0196
  · exact transition0197
  · exact transition0198
  · exact transition0199
  · exact transition0200
  · exact transition0201
  · exact transition0202
  · exact transition0203
  · exact transition0204
  · exact transition0205
  · exact transition0206
  · exact transition0207
  · exact transition0208
  · exact transition0209
  · exact transition0210
  · exact transition0211
  · exact transition0212
  · exact transition0213
  · exact transition0214
  · exact transition0215
  · exact transition0216
  · exact transition0217
  · exact transition0218
  · exact transition0219
  · exact transition0220
  · exact transition0221
  · exact transition0222
  · exact transition0223
  · exact transition0224
  · exact transition0225
  · exact transition0226
  · exact transition0227
  · exact transition0228
  · exact transition0229
  · exact transition0230
  · exact transition0231
  · exact transition0232
  · exact transition0233
  · exact transition0234
  · exact transition0235
  · exact transition0236
  · exact transition0237
  · exact transition0238
  · exact transition0239
  · exact transition0240
  · exact transition0241
  · exact transition0242
  · exact transition0243
  · exact transition0244
  · exact transition0245
  · exact transition0246
  · exact transition0247
  · exact transition0248
  · exact transition0249
  · exact transition0250
  · exact transition0251
  · exact transition0252
  · exact transition0253
  · exact transition0254
  · exact transition0255

end
end ErdosOverlap.Native6Grid
