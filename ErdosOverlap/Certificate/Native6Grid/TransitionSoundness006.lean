/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck048
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck049
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck050
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck051
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck052
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck053
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck054
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck055

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk006 (j : ℕ) (hlo : 384 ≤ j) (hhi : j < 448) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0384
  · exact transition0385
  · exact transition0386
  · exact transition0387
  · exact transition0388
  · exact transition0389
  · exact transition0390
  · exact transition0391
  · exact transition0392
  · exact transition0393
  · exact transition0394
  · exact transition0395
  · exact transition0396
  · exact transition0397
  · exact transition0398
  · exact transition0399
  · exact transition0400
  · exact transition0401
  · exact transition0402
  · exact transition0403
  · exact transition0404
  · exact transition0405
  · exact transition0406
  · exact transition0407
  · exact transition0408
  · exact transition0409
  · exact transition0410
  · exact transition0411
  · exact transition0412
  · exact transition0413
  · exact transition0414
  · exact transition0415
  · exact transition0416
  · exact transition0417
  · exact transition0418
  · exact transition0419
  · exact transition0420
  · exact transition0421
  · exact transition0422
  · exact transition0423
  · exact transition0424
  · exact transition0425
  · exact transition0426
  · exact transition0427
  · exact transition0428
  · exact transition0429
  · exact transition0430
  · exact transition0431
  · exact transition0432
  · exact transition0433
  · exact transition0434
  · exact transition0435
  · exact transition0436
  · exact transition0437
  · exact transition0438
  · exact transition0439
  · exact transition0440
  · exact transition0441
  · exact transition0442
  · exact transition0443
  · exact transition0444
  · exact transition0445
  · exact transition0446
  · exact transition0447

end
end ErdosOverlap.Native6Grid
