/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck056
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck057
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck058
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck059
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck060
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck061
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck062
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck063

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk007 (j : ℕ) (hlo : 448 ≤ j) (hhi : j < 512) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0448
  · exact transition0449
  · exact transition0450
  · exact transition0451
  · exact transition0452
  · exact transition0453
  · exact transition0454
  · exact transition0455
  · exact transition0456
  · exact transition0457
  · exact transition0458
  · exact transition0459
  · exact transition0460
  · exact transition0461
  · exact transition0462
  · exact transition0463
  · exact transition0464
  · exact transition0465
  · exact transition0466
  · exact transition0467
  · exact transition0468
  · exact transition0469
  · exact transition0470
  · exact transition0471
  · exact transition0472
  · exact transition0473
  · exact transition0474
  · exact transition0475
  · exact transition0476
  · exact transition0477
  · exact transition0478
  · exact transition0479
  · exact transition0480
  · exact transition0481
  · exact transition0482
  · exact transition0483
  · exact transition0484
  · exact transition0485
  · exact transition0486
  · exact transition0487
  · exact transition0488
  · exact transition0489
  · exact transition0490
  · exact transition0491
  · exact transition0492
  · exact transition0493
  · exact transition0494
  · exact transition0495
  · exact transition0496
  · exact transition0497
  · exact transition0498
  · exact transition0499
  · exact transition0500
  · exact transition0501
  · exact transition0502
  · exact transition0503
  · exact transition0504
  · exact transition0505
  · exact transition0506
  · exact transition0507
  · exact transition0508
  · exact transition0509
  · exact transition0510
  · exact transition0511

end
end ErdosOverlap.Native6Grid
