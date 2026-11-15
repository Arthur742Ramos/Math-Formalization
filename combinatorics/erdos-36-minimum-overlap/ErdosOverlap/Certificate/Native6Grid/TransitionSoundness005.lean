/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck040
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck041
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck042
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck043
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck044
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck045
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck046
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck047

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk005 (j : ℕ) (hlo : 320 ≤ j) (hhi : j < 384) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0320
  · exact transition0321
  · exact transition0322
  · exact transition0323
  · exact transition0324
  · exact transition0325
  · exact transition0326
  · exact transition0327
  · exact transition0328
  · exact transition0329
  · exact transition0330
  · exact transition0331
  · exact transition0332
  · exact transition0333
  · exact transition0334
  · exact transition0335
  · exact transition0336
  · exact transition0337
  · exact transition0338
  · exact transition0339
  · exact transition0340
  · exact transition0341
  · exact transition0342
  · exact transition0343
  · exact transition0344
  · exact transition0345
  · exact transition0346
  · exact transition0347
  · exact transition0348
  · exact transition0349
  · exact transition0350
  · exact transition0351
  · exact transition0352
  · exact transition0353
  · exact transition0354
  · exact transition0355
  · exact transition0356
  · exact transition0357
  · exact transition0358
  · exact transition0359
  · exact transition0360
  · exact transition0361
  · exact transition0362
  · exact transition0363
  · exact transition0364
  · exact transition0365
  · exact transition0366
  · exact transition0367
  · exact transition0368
  · exact transition0369
  · exact transition0370
  · exact transition0371
  · exact transition0372
  · exact transition0373
  · exact transition0374
  · exact transition0375
  · exact transition0376
  · exact transition0377
  · exact transition0378
  · exact transition0379
  · exact transition0380
  · exact transition0381
  · exact transition0382
  · exact transition0383

end
end ErdosOverlap.Native6Grid
