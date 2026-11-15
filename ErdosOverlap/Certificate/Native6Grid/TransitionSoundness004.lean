/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck032
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck033
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck034
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck035
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck036
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck037
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck038
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck039

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk004 (j : ℕ) (hlo : 256 ≤ j) (hhi : j < 320) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0256
  · exact transition0257
  · exact transition0258
  · exact transition0259
  · exact transition0260
  · exact transition0261
  · exact transition0262
  · exact transition0263
  · exact transition0264
  · exact transition0265
  · exact transition0266
  · exact transition0267
  · exact transition0268
  · exact transition0269
  · exact transition0270
  · exact transition0271
  · exact transition0272
  · exact transition0273
  · exact transition0274
  · exact transition0275
  · exact transition0276
  · exact transition0277
  · exact transition0278
  · exact transition0279
  · exact transition0280
  · exact transition0281
  · exact transition0282
  · exact transition0283
  · exact transition0284
  · exact transition0285
  · exact transition0286
  · exact transition0287
  · exact transition0288
  · exact transition0289
  · exact transition0290
  · exact transition0291
  · exact transition0292
  · exact transition0293
  · exact transition0294
  · exact transition0295
  · exact transition0296
  · exact transition0297
  · exact transition0298
  · exact transition0299
  · exact transition0300
  · exact transition0301
  · exact transition0302
  · exact transition0303
  · exact transition0304
  · exact transition0305
  · exact transition0306
  · exact transition0307
  · exact transition0308
  · exact transition0309
  · exact transition0310
  · exact transition0311
  · exact transition0312
  · exact transition0313
  · exact transition0314
  · exact transition0315
  · exact transition0316
  · exact transition0317
  · exact transition0318
  · exact transition0319

end
end ErdosOverlap.Native6Grid
