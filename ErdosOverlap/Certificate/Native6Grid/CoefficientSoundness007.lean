/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck056
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck057
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck058
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck059
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck060
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck061
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck062
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck063

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk007 (j : ℕ) (hlo : 448 ≤ j) (hhi : j < 512) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0448
  · exact coefficientCheck0449
  · exact coefficientCheck0450
  · exact coefficientCheck0451
  · exact coefficientCheck0452
  · exact coefficientCheck0453
  · exact coefficientCheck0454
  · exact coefficientCheck0455
  · exact coefficientCheck0456
  · exact coefficientCheck0457
  · exact coefficientCheck0458
  · exact coefficientCheck0459
  · exact coefficientCheck0460
  · exact coefficientCheck0461
  · exact coefficientCheck0462
  · exact coefficientCheck0463
  · exact coefficientCheck0464
  · exact coefficientCheck0465
  · exact coefficientCheck0466
  · exact coefficientCheck0467
  · exact coefficientCheck0468
  · exact coefficientCheck0469
  · exact coefficientCheck0470
  · exact coefficientCheck0471
  · exact coefficientCheck0472
  · exact coefficientCheck0473
  · exact coefficientCheck0474
  · exact coefficientCheck0475
  · exact coefficientCheck0476
  · exact coefficientCheck0477
  · exact coefficientCheck0478
  · exact coefficientCheck0479
  · exact coefficientCheck0480
  · exact coefficientCheck0481
  · exact coefficientCheck0482
  · exact coefficientCheck0483
  · exact coefficientCheck0484
  · exact coefficientCheck0485
  · exact coefficientCheck0486
  · exact coefficientCheck0487
  · exact coefficientCheck0488
  · exact coefficientCheck0489
  · exact coefficientCheck0490
  · exact coefficientCheck0491
  · exact coefficientCheck0492
  · exact coefficientCheck0493
  · exact coefficientCheck0494
  · exact coefficientCheck0495
  · exact coefficientCheck0496
  · exact coefficientCheck0497
  · exact coefficientCheck0498
  · exact coefficientCheck0499
  · exact coefficientCheck0500
  · exact coefficientCheck0501
  · exact coefficientCheck0502
  · exact coefficientCheck0503
  · exact coefficientCheck0504
  · exact coefficientCheck0505
  · exact coefficientCheck0506
  · exact coefficientCheck0507
  · exact coefficientCheck0508
  · exact coefficientCheck0509
  · exact coefficientCheck0510
  · exact coefficientCheck0511

end
end ErdosOverlap.Native6Grid
