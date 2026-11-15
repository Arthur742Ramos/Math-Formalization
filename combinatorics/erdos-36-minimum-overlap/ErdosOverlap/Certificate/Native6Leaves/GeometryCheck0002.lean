/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0004
public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0005
public import ErdosOverlap.Certificate.Native6Leaves.GeometryTraceData0002
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0006
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0007
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0008
public import ErdosOverlap.Numerics.NativePolynomialDirectTrace

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def checkedGeometry00512 : CheckedGeometry :=
  ⟨geometry00512, Geometry.check_of_directTraceCheck geometry00512
    checkedPatchCache0420 checkedPatchCache0421
    geometryTraceA00512 geometryTraceB00512 (by decide +kernel)⟩

def checkedGeometry00513 : CheckedGeometry :=
  ⟨geometry00513, Geometry.check_of_directTraceCheck geometry00513
    checkedPatchCache0422 checkedPatchCache0423
    geometryTraceA00513 geometryTraceB00513 (by decide +kernel)⟩

def checkedGeometry00514 : CheckedGeometry :=
  ⟨geometry00514, Geometry.check_of_directTraceCheck geometry00514
    checkedPatchCache0424 checkedPatchCache0425
    geometryTraceA00514 geometryTraceB00514 (by decide +kernel)⟩

def checkedGeometry00515 : CheckedGeometry :=
  ⟨geometry00515, Geometry.check_of_directTraceCheck geometry00515
    checkedPatchCache0426 checkedPatchCache0427
    geometryTraceA00515 geometryTraceB00515 (by decide +kernel)⟩

def checkedGeometry00516 : CheckedGeometry :=
  ⟨geometry00516, Geometry.check_of_directTraceCheck geometry00516
    checkedPatchCache0428 checkedPatchCache0429
    geometryTraceA00516 geometryTraceB00516 (by decide +kernel)⟩

def checkedGeometry00517 : CheckedGeometry :=
  ⟨geometry00517, Geometry.check_of_directTraceCheck geometry00517
    checkedPatchCache0430 checkedPatchCache0431
    geometryTraceA00517 geometryTraceB00517 (by decide +kernel)⟩

def checkedGeometry00518 : CheckedGeometry :=
  ⟨geometry00518, Geometry.check_of_directTraceCheck geometry00518
    checkedPatchCache0432 checkedPatchCache0433
    geometryTraceA00518 geometryTraceB00518 (by decide +kernel)⟩

def checkedGeometry00519 : CheckedGeometry :=
  ⟨geometry00519, Geometry.check_of_directTraceCheck geometry00519
    checkedPatchCache0434 checkedPatchCache0435
    geometryTraceA00519 geometryTraceB00519 (by decide +kernel)⟩

def checkedGeometry00520 : CheckedGeometry :=
  ⟨geometry00520, Geometry.check_of_directTraceCheck geometry00520
    checkedPatchCache0436 checkedPatchCache0437
    geometryTraceA00520 geometryTraceB00520 (by decide +kernel)⟩

def checkedGeometry00521 : CheckedGeometry :=
  ⟨geometry00521, Geometry.check_of_directTraceCheck geometry00521
    checkedPatchCache0438 checkedPatchCache0439
    geometryTraceA00521 geometryTraceB00521 (by decide +kernel)⟩

def checkedGeometry00522 : CheckedGeometry :=
  ⟨geometry00522, Geometry.check_of_directTraceCheck geometry00522
    checkedPatchCache0440 checkedPatchCache0441
    geometryTraceA00522 geometryTraceB00522 (by decide +kernel)⟩

def checkedGeometry00523 : CheckedGeometry :=
  ⟨geometry00523, Geometry.check_of_directTraceCheck geometry00523
    checkedPatchCache0442 checkedPatchCache0443
    geometryTraceA00523 geometryTraceB00523 (by decide +kernel)⟩

def checkedGeometry00524 : CheckedGeometry :=
  ⟨geometry00524, Geometry.check_of_directTraceCheck geometry00524
    checkedPatchCache0444 checkedPatchCache0445
    geometryTraceA00524 geometryTraceB00524 (by decide +kernel)⟩

def checkedGeometry00525 : CheckedGeometry :=
  ⟨geometry00525, Geometry.check_of_directTraceCheck geometry00525
    checkedPatchCache0446 checkedPatchCache0447
    geometryTraceA00525 geometryTraceB00525 (by decide +kernel)⟩

def checkedGeometry00526 : CheckedGeometry :=
  ⟨geometry00526, Geometry.check_of_directTraceCheck geometry00526
    checkedPatchCache0448 checkedPatchCache0449
    geometryTraceA00526 geometryTraceB00526 (by decide +kernel)⟩

def checkedGeometry00527 : CheckedGeometry :=
  ⟨geometry00527, Geometry.check_of_directTraceCheck geometry00527
    checkedPatchCache0450 checkedPatchCache0451
    geometryTraceA00527 geometryTraceB00527 (by decide +kernel)⟩

def checkedGeometry00528 : CheckedGeometry :=
  ⟨geometry00528, Geometry.check_of_directTraceCheck geometry00528
    checkedPatchCache0452 checkedPatchCache0453
    geometryTraceA00528 geometryTraceB00528 (by decide +kernel)⟩

def checkedGeometry00529 : CheckedGeometry :=
  ⟨geometry00529, Geometry.check_of_directTraceCheck geometry00529
    checkedPatchCache0454 checkedPatchCache0455
    geometryTraceA00529 geometryTraceB00529 (by decide +kernel)⟩

def checkedGeometry00530 : CheckedGeometry :=
  ⟨geometry00530, Geometry.check_of_directTraceCheck geometry00530
    checkedPatchCache0456 checkedPatchCache0457
    geometryTraceA00530 geometryTraceB00530 (by decide +kernel)⟩

def checkedGeometry00531 : CheckedGeometry :=
  ⟨geometry00531, Geometry.check_of_directTraceCheck geometry00531
    checkedPatchCache0458 checkedPatchCache0459
    geometryTraceA00531 geometryTraceB00531 (by decide +kernel)⟩

def checkedGeometry00532 : CheckedGeometry :=
  ⟨geometry00532, Geometry.check_of_directTraceCheck geometry00532
    checkedPatchCache0458 checkedPatchCache0459
    geometryTraceA00532 geometryTraceB00532 (by decide +kernel)⟩

def checkedGeometry00533 : CheckedGeometry :=
  ⟨geometry00533, Geometry.check_of_directTraceCheck geometry00533
    checkedPatchCache0458 checkedPatchCache0459
    geometryTraceA00533 geometryTraceB00533 (by decide +kernel)⟩

def checkedGeometry00534 : CheckedGeometry :=
  ⟨geometry00534, Geometry.check_of_directTraceCheck geometry00534
    checkedPatchCache0460 checkedPatchCache0461
    geometryTraceA00534 geometryTraceB00534 (by decide +kernel)⟩

def checkedGeometry00535 : CheckedGeometry :=
  ⟨geometry00535, Geometry.check_of_directTraceCheck geometry00535
    checkedPatchCache0460 checkedPatchCache0461
    geometryTraceA00535 geometryTraceB00535 (by decide +kernel)⟩

def checkedGeometry00536 : CheckedGeometry :=
  ⟨geometry00536, Geometry.check_of_directTraceCheck geometry00536
    checkedPatchCache0460 checkedPatchCache0461
    geometryTraceA00536 geometryTraceB00536 (by decide +kernel)⟩

def checkedGeometry00537 : CheckedGeometry :=
  ⟨geometry00537, Geometry.check_of_directTraceCheck geometry00537
    checkedPatchCache0460 checkedPatchCache0461
    geometryTraceA00537 geometryTraceB00537 (by decide +kernel)⟩

def checkedGeometry00538 : CheckedGeometry :=
  ⟨geometry00538, Geometry.check_of_directTraceCheck geometry00538
    checkedPatchCache0460 checkedPatchCache0461
    geometryTraceA00538 geometryTraceB00538 (by decide +kernel)⟩

def checkedGeometry00539 : CheckedGeometry :=
  ⟨geometry00539, Geometry.check_of_directTraceCheck geometry00539
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00539 geometryTraceB00539 (by decide +kernel)⟩

def checkedGeometry00540 : CheckedGeometry :=
  ⟨geometry00540, Geometry.check_of_directTraceCheck geometry00540
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00540 geometryTraceB00540 (by decide +kernel)⟩

def checkedGeometry00541 : CheckedGeometry :=
  ⟨geometry00541, Geometry.check_of_directTraceCheck geometry00541
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00541 geometryTraceB00541 (by decide +kernel)⟩

def checkedGeometry00542 : CheckedGeometry :=
  ⟨geometry00542, Geometry.check_of_directTraceCheck geometry00542
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00542 geometryTraceB00542 (by decide +kernel)⟩

def checkedGeometry00543 : CheckedGeometry :=
  ⟨geometry00543, Geometry.check_of_directTraceCheck geometry00543
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00543 geometryTraceB00543 (by decide +kernel)⟩

def checkedGeometry00544 : CheckedGeometry :=
  ⟨geometry00544, Geometry.check_of_directTraceCheck geometry00544
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00544 geometryTraceB00544 (by decide +kernel)⟩

def checkedGeometry00545 : CheckedGeometry :=
  ⟨geometry00545, Geometry.check_of_directTraceCheck geometry00545
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00545 geometryTraceB00545 (by decide +kernel)⟩

def checkedGeometry00546 : CheckedGeometry :=
  ⟨geometry00546, Geometry.check_of_directTraceCheck geometry00546
    checkedPatchCache0462 checkedPatchCache0463
    geometryTraceA00546 geometryTraceB00546 (by decide +kernel)⟩

def checkedGeometry00547 : CheckedGeometry :=
  ⟨geometry00547, Geometry.check_of_directTraceCheck geometry00547
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00547 geometryTraceB00547 (by decide +kernel)⟩

def checkedGeometry00548 : CheckedGeometry :=
  ⟨geometry00548, Geometry.check_of_directTraceCheck geometry00548
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00548 geometryTraceB00548 (by decide +kernel)⟩

def checkedGeometry00549 : CheckedGeometry :=
  ⟨geometry00549, Geometry.check_of_directTraceCheck geometry00549
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00549 geometryTraceB00549 (by decide +kernel)⟩

def checkedGeometry00550 : CheckedGeometry :=
  ⟨geometry00550, Geometry.check_of_directTraceCheck geometry00550
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00550 geometryTraceB00550 (by decide +kernel)⟩

def checkedGeometry00551 : CheckedGeometry :=
  ⟨geometry00551, Geometry.check_of_directTraceCheck geometry00551
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00551 geometryTraceB00551 (by decide +kernel)⟩

def checkedGeometry00552 : CheckedGeometry :=
  ⟨geometry00552, Geometry.check_of_directTraceCheck geometry00552
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00552 geometryTraceB00552 (by decide +kernel)⟩

def checkedGeometry00553 : CheckedGeometry :=
  ⟨geometry00553, Geometry.check_of_directTraceCheck geometry00553
    checkedPatchCache0464 checkedPatchCache0465
    geometryTraceA00553 geometryTraceB00553 (by decide +kernel)⟩

def checkedGeometry00554 : CheckedGeometry :=
  ⟨geometry00554, Geometry.check_of_directTraceCheck geometry00554
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00554 geometryTraceB00554 (by decide +kernel)⟩

def checkedGeometry00555 : CheckedGeometry :=
  ⟨geometry00555, Geometry.check_of_directTraceCheck geometry00555
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00555 geometryTraceB00555 (by decide +kernel)⟩

def checkedGeometry00556 : CheckedGeometry :=
  ⟨geometry00556, Geometry.check_of_directTraceCheck geometry00556
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00556 geometryTraceB00556 (by decide +kernel)⟩

def checkedGeometry00557 : CheckedGeometry :=
  ⟨geometry00557, Geometry.check_of_directTraceCheck geometry00557
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00557 geometryTraceB00557 (by decide +kernel)⟩

def checkedGeometry00558 : CheckedGeometry :=
  ⟨geometry00558, Geometry.check_of_directTraceCheck geometry00558
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00558 geometryTraceB00558 (by decide +kernel)⟩

def checkedGeometry00559 : CheckedGeometry :=
  ⟨geometry00559, Geometry.check_of_directTraceCheck geometry00559
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00559 geometryTraceB00559 (by decide +kernel)⟩

def checkedGeometry00560 : CheckedGeometry :=
  ⟨geometry00560, Geometry.check_of_directTraceCheck geometry00560
    checkedPatchCache0466 checkedPatchCache0467
    geometryTraceA00560 geometryTraceB00560 (by decide +kernel)⟩

def checkedGeometry00561 : CheckedGeometry :=
  ⟨geometry00561, Geometry.check_of_directTraceCheck geometry00561
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00561 geometryTraceB00561 (by decide +kernel)⟩

def checkedGeometry00562 : CheckedGeometry :=
  ⟨geometry00562, Geometry.check_of_directTraceCheck geometry00562
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00562 geometryTraceB00562 (by decide +kernel)⟩

def checkedGeometry00563 : CheckedGeometry :=
  ⟨geometry00563, Geometry.check_of_directTraceCheck geometry00563
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00563 geometryTraceB00563 (by decide +kernel)⟩

def checkedGeometry00564 : CheckedGeometry :=
  ⟨geometry00564, Geometry.check_of_directTraceCheck geometry00564
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00564 geometryTraceB00564 (by decide +kernel)⟩

def checkedGeometry00565 : CheckedGeometry :=
  ⟨geometry00565, Geometry.check_of_directTraceCheck geometry00565
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00565 geometryTraceB00565 (by decide +kernel)⟩

def checkedGeometry00566 : CheckedGeometry :=
  ⟨geometry00566, Geometry.check_of_directTraceCheck geometry00566
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00566 geometryTraceB00566 (by decide +kernel)⟩

def checkedGeometry00567 : CheckedGeometry :=
  ⟨geometry00567, Geometry.check_of_directTraceCheck geometry00567
    checkedPatchCache0468 checkedPatchCache0469
    geometryTraceA00567 geometryTraceB00567 (by decide +kernel)⟩

def checkedGeometry00568 : CheckedGeometry :=
  ⟨geometry00568, Geometry.check_of_directTraceCheck geometry00568
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00568 geometryTraceB00568 (by decide +kernel)⟩

def checkedGeometry00569 : CheckedGeometry :=
  ⟨geometry00569, Geometry.check_of_directTraceCheck geometry00569
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00569 geometryTraceB00569 (by decide +kernel)⟩

def checkedGeometry00570 : CheckedGeometry :=
  ⟨geometry00570, Geometry.check_of_directTraceCheck geometry00570
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00570 geometryTraceB00570 (by decide +kernel)⟩

def checkedGeometry00571 : CheckedGeometry :=
  ⟨geometry00571, Geometry.check_of_directTraceCheck geometry00571
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00571 geometryTraceB00571 (by decide +kernel)⟩

def checkedGeometry00572 : CheckedGeometry :=
  ⟨geometry00572, Geometry.check_of_directTraceCheck geometry00572
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00572 geometryTraceB00572 (by decide +kernel)⟩

def checkedGeometry00573 : CheckedGeometry :=
  ⟨geometry00573, Geometry.check_of_directTraceCheck geometry00573
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00573 geometryTraceB00573 (by decide +kernel)⟩

def checkedGeometry00574 : CheckedGeometry :=
  ⟨geometry00574, Geometry.check_of_directTraceCheck geometry00574
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00574 geometryTraceB00574 (by decide +kernel)⟩

def checkedGeometry00575 : CheckedGeometry :=
  ⟨geometry00575, Geometry.check_of_directTraceCheck geometry00575
    checkedPatchCache0470 checkedPatchCache0471
    geometryTraceA00575 geometryTraceB00575 (by decide +kernel)⟩

def checkedGeometry00576 : CheckedGeometry :=
  ⟨geometry00576, Geometry.check_of_directTraceCheck geometry00576
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00576 geometryTraceB00576 (by decide +kernel)⟩

def checkedGeometry00577 : CheckedGeometry :=
  ⟨geometry00577, Geometry.check_of_directTraceCheck geometry00577
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00577 geometryTraceB00577 (by decide +kernel)⟩

def checkedGeometry00578 : CheckedGeometry :=
  ⟨geometry00578, Geometry.check_of_directTraceCheck geometry00578
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00578 geometryTraceB00578 (by decide +kernel)⟩

def checkedGeometry00579 : CheckedGeometry :=
  ⟨geometry00579, Geometry.check_of_directTraceCheck geometry00579
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00579 geometryTraceB00579 (by decide +kernel)⟩

def checkedGeometry00580 : CheckedGeometry :=
  ⟨geometry00580, Geometry.check_of_directTraceCheck geometry00580
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00580 geometryTraceB00580 (by decide +kernel)⟩

def checkedGeometry00581 : CheckedGeometry :=
  ⟨geometry00581, Geometry.check_of_directTraceCheck geometry00581
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00581 geometryTraceB00581 (by decide +kernel)⟩

def checkedGeometry00582 : CheckedGeometry :=
  ⟨geometry00582, Geometry.check_of_directTraceCheck geometry00582
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00582 geometryTraceB00582 (by decide +kernel)⟩

def checkedGeometry00583 : CheckedGeometry :=
  ⟨geometry00583, Geometry.check_of_directTraceCheck geometry00583
    checkedPatchCache0472 checkedPatchCache0473
    geometryTraceA00583 geometryTraceB00583 (by decide +kernel)⟩

def checkedGeometry00584 : CheckedGeometry :=
  ⟨geometry00584, Geometry.check_of_directTraceCheck geometry00584
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00584 geometryTraceB00584 (by decide +kernel)⟩

def checkedGeometry00585 : CheckedGeometry :=
  ⟨geometry00585, Geometry.check_of_directTraceCheck geometry00585
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00585 geometryTraceB00585 (by decide +kernel)⟩

def checkedGeometry00586 : CheckedGeometry :=
  ⟨geometry00586, Geometry.check_of_directTraceCheck geometry00586
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00586 geometryTraceB00586 (by decide +kernel)⟩

def checkedGeometry00587 : CheckedGeometry :=
  ⟨geometry00587, Geometry.check_of_directTraceCheck geometry00587
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00587 geometryTraceB00587 (by decide +kernel)⟩

def checkedGeometry00588 : CheckedGeometry :=
  ⟨geometry00588, Geometry.check_of_directTraceCheck geometry00588
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00588 geometryTraceB00588 (by decide +kernel)⟩

def checkedGeometry00589 : CheckedGeometry :=
  ⟨geometry00589, Geometry.check_of_directTraceCheck geometry00589
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00589 geometryTraceB00589 (by decide +kernel)⟩

def checkedGeometry00590 : CheckedGeometry :=
  ⟨geometry00590, Geometry.check_of_directTraceCheck geometry00590
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00590 geometryTraceB00590 (by decide +kernel)⟩

def checkedGeometry00591 : CheckedGeometry :=
  ⟨geometry00591, Geometry.check_of_directTraceCheck geometry00591
    checkedPatchCache0474 checkedPatchCache0475
    geometryTraceA00591 geometryTraceB00591 (by decide +kernel)⟩

def checkedGeometry00592 : CheckedGeometry :=
  ⟨geometry00592, Geometry.check_of_directTraceCheck geometry00592
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00592 geometryTraceB00592 (by decide +kernel)⟩

def checkedGeometry00593 : CheckedGeometry :=
  ⟨geometry00593, Geometry.check_of_directTraceCheck geometry00593
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00593 geometryTraceB00593 (by decide +kernel)⟩

def checkedGeometry00594 : CheckedGeometry :=
  ⟨geometry00594, Geometry.check_of_directTraceCheck geometry00594
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00594 geometryTraceB00594 (by decide +kernel)⟩

def checkedGeometry00595 : CheckedGeometry :=
  ⟨geometry00595, Geometry.check_of_directTraceCheck geometry00595
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00595 geometryTraceB00595 (by decide +kernel)⟩

def checkedGeometry00596 : CheckedGeometry :=
  ⟨geometry00596, Geometry.check_of_directTraceCheck geometry00596
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00596 geometryTraceB00596 (by decide +kernel)⟩

def checkedGeometry00597 : CheckedGeometry :=
  ⟨geometry00597, Geometry.check_of_directTraceCheck geometry00597
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00597 geometryTraceB00597 (by decide +kernel)⟩

def checkedGeometry00598 : CheckedGeometry :=
  ⟨geometry00598, Geometry.check_of_directTraceCheck geometry00598
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00598 geometryTraceB00598 (by decide +kernel)⟩

def checkedGeometry00599 : CheckedGeometry :=
  ⟨geometry00599, Geometry.check_of_directTraceCheck geometry00599
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00599 geometryTraceB00599 (by decide +kernel)⟩

def checkedGeometry00600 : CheckedGeometry :=
  ⟨geometry00600, Geometry.check_of_directTraceCheck geometry00600
    checkedPatchCache0476 checkedPatchCache0477
    geometryTraceA00600 geometryTraceB00600 (by decide +kernel)⟩

def checkedGeometry00601 : CheckedGeometry :=
  ⟨geometry00601, Geometry.check_of_directTraceCheck geometry00601
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00601 geometryTraceB00601 (by decide +kernel)⟩

def checkedGeometry00602 : CheckedGeometry :=
  ⟨geometry00602, Geometry.check_of_directTraceCheck geometry00602
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00602 geometryTraceB00602 (by decide +kernel)⟩

def checkedGeometry00603 : CheckedGeometry :=
  ⟨geometry00603, Geometry.check_of_directTraceCheck geometry00603
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00603 geometryTraceB00603 (by decide +kernel)⟩

def checkedGeometry00604 : CheckedGeometry :=
  ⟨geometry00604, Geometry.check_of_directTraceCheck geometry00604
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00604 geometryTraceB00604 (by decide +kernel)⟩

def checkedGeometry00605 : CheckedGeometry :=
  ⟨geometry00605, Geometry.check_of_directTraceCheck geometry00605
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00605 geometryTraceB00605 (by decide +kernel)⟩

def checkedGeometry00606 : CheckedGeometry :=
  ⟨geometry00606, Geometry.check_of_directTraceCheck geometry00606
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00606 geometryTraceB00606 (by decide +kernel)⟩

def checkedGeometry00607 : CheckedGeometry :=
  ⟨geometry00607, Geometry.check_of_directTraceCheck geometry00607
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00607 geometryTraceB00607 (by decide +kernel)⟩

def checkedGeometry00608 : CheckedGeometry :=
  ⟨geometry00608, Geometry.check_of_directTraceCheck geometry00608
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00608 geometryTraceB00608 (by decide +kernel)⟩

def checkedGeometry00609 : CheckedGeometry :=
  ⟨geometry00609, Geometry.check_of_directTraceCheck geometry00609
    checkedPatchCache0478 checkedPatchCache0479
    geometryTraceA00609 geometryTraceB00609 (by decide +kernel)⟩

def checkedGeometry00610 : CheckedGeometry :=
  ⟨geometry00610, Geometry.check_of_directTraceCheck geometry00610
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00610 geometryTraceB00610 (by decide +kernel)⟩

def checkedGeometry00611 : CheckedGeometry :=
  ⟨geometry00611, Geometry.check_of_directTraceCheck geometry00611
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00611 geometryTraceB00611 (by decide +kernel)⟩

def checkedGeometry00612 : CheckedGeometry :=
  ⟨geometry00612, Geometry.check_of_directTraceCheck geometry00612
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00612 geometryTraceB00612 (by decide +kernel)⟩

def checkedGeometry00613 : CheckedGeometry :=
  ⟨geometry00613, Geometry.check_of_directTraceCheck geometry00613
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00613 geometryTraceB00613 (by decide +kernel)⟩

def checkedGeometry00614 : CheckedGeometry :=
  ⟨geometry00614, Geometry.check_of_directTraceCheck geometry00614
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00614 geometryTraceB00614 (by decide +kernel)⟩

def checkedGeometry00615 : CheckedGeometry :=
  ⟨geometry00615, Geometry.check_of_directTraceCheck geometry00615
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00615 geometryTraceB00615 (by decide +kernel)⟩

def checkedGeometry00616 : CheckedGeometry :=
  ⟨geometry00616, Geometry.check_of_directTraceCheck geometry00616
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00616 geometryTraceB00616 (by decide +kernel)⟩

def checkedGeometry00617 : CheckedGeometry :=
  ⟨geometry00617, Geometry.check_of_directTraceCheck geometry00617
    checkedPatchCache0480 checkedPatchCache0481
    geometryTraceA00617 geometryTraceB00617 (by decide +kernel)⟩

def checkedGeometry00618 : CheckedGeometry :=
  ⟨geometry00618, Geometry.check_of_directTraceCheck geometry00618
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00618 geometryTraceB00618 (by decide +kernel)⟩

def checkedGeometry00619 : CheckedGeometry :=
  ⟨geometry00619, Geometry.check_of_directTraceCheck geometry00619
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00619 geometryTraceB00619 (by decide +kernel)⟩

def checkedGeometry00620 : CheckedGeometry :=
  ⟨geometry00620, Geometry.check_of_directTraceCheck geometry00620
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00620 geometryTraceB00620 (by decide +kernel)⟩

def checkedGeometry00621 : CheckedGeometry :=
  ⟨geometry00621, Geometry.check_of_directTraceCheck geometry00621
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00621 geometryTraceB00621 (by decide +kernel)⟩

def checkedGeometry00622 : CheckedGeometry :=
  ⟨geometry00622, Geometry.check_of_directTraceCheck geometry00622
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00622 geometryTraceB00622 (by decide +kernel)⟩

def checkedGeometry00623 : CheckedGeometry :=
  ⟨geometry00623, Geometry.check_of_directTraceCheck geometry00623
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00623 geometryTraceB00623 (by decide +kernel)⟩

def checkedGeometry00624 : CheckedGeometry :=
  ⟨geometry00624, Geometry.check_of_directTraceCheck geometry00624
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00624 geometryTraceB00624 (by decide +kernel)⟩

def checkedGeometry00625 : CheckedGeometry :=
  ⟨geometry00625, Geometry.check_of_directTraceCheck geometry00625
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00625 geometryTraceB00625 (by decide +kernel)⟩

def checkedGeometry00626 : CheckedGeometry :=
  ⟨geometry00626, Geometry.check_of_directTraceCheck geometry00626
    checkedPatchCache0482 checkedPatchCache0483
    geometryTraceA00626 geometryTraceB00626 (by decide +kernel)⟩

def checkedGeometry00627 : CheckedGeometry :=
  ⟨geometry00627, Geometry.check_of_directTraceCheck geometry00627
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00627 geometryTraceB00627 (by decide +kernel)⟩

def checkedGeometry00628 : CheckedGeometry :=
  ⟨geometry00628, Geometry.check_of_directTraceCheck geometry00628
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00628 geometryTraceB00628 (by decide +kernel)⟩

def checkedGeometry00629 : CheckedGeometry :=
  ⟨geometry00629, Geometry.check_of_directTraceCheck geometry00629
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00629 geometryTraceB00629 (by decide +kernel)⟩

def checkedGeometry00630 : CheckedGeometry :=
  ⟨geometry00630, Geometry.check_of_directTraceCheck geometry00630
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00630 geometryTraceB00630 (by decide +kernel)⟩

def checkedGeometry00631 : CheckedGeometry :=
  ⟨geometry00631, Geometry.check_of_directTraceCheck geometry00631
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00631 geometryTraceB00631 (by decide +kernel)⟩

def checkedGeometry00632 : CheckedGeometry :=
  ⟨geometry00632, Geometry.check_of_directTraceCheck geometry00632
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00632 geometryTraceB00632 (by decide +kernel)⟩

def checkedGeometry00633 : CheckedGeometry :=
  ⟨geometry00633, Geometry.check_of_directTraceCheck geometry00633
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00633 geometryTraceB00633 (by decide +kernel)⟩

def checkedGeometry00634 : CheckedGeometry :=
  ⟨geometry00634, Geometry.check_of_directTraceCheck geometry00634
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00634 geometryTraceB00634 (by decide +kernel)⟩

def checkedGeometry00635 : CheckedGeometry :=
  ⟨geometry00635, Geometry.check_of_directTraceCheck geometry00635
    checkedPatchCache0484 checkedPatchCache0485
    geometryTraceA00635 geometryTraceB00635 (by decide +kernel)⟩

def checkedGeometry00636 : CheckedGeometry :=
  ⟨geometry00636, Geometry.check_of_directTraceCheck geometry00636
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00636 geometryTraceB00636 (by decide +kernel)⟩

def checkedGeometry00637 : CheckedGeometry :=
  ⟨geometry00637, Geometry.check_of_directTraceCheck geometry00637
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00637 geometryTraceB00637 (by decide +kernel)⟩

def checkedGeometry00638 : CheckedGeometry :=
  ⟨geometry00638, Geometry.check_of_directTraceCheck geometry00638
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00638 geometryTraceB00638 (by decide +kernel)⟩

def checkedGeometry00639 : CheckedGeometry :=
  ⟨geometry00639, Geometry.check_of_directTraceCheck geometry00639
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00639 geometryTraceB00639 (by decide +kernel)⟩

def checkedGeometry00640 : CheckedGeometry :=
  ⟨geometry00640, Geometry.check_of_directTraceCheck geometry00640
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00640 geometryTraceB00640 (by decide +kernel)⟩

def checkedGeometry00641 : CheckedGeometry :=
  ⟨geometry00641, Geometry.check_of_directTraceCheck geometry00641
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00641 geometryTraceB00641 (by decide +kernel)⟩

def checkedGeometry00642 : CheckedGeometry :=
  ⟨geometry00642, Geometry.check_of_directTraceCheck geometry00642
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00642 geometryTraceB00642 (by decide +kernel)⟩

def checkedGeometry00643 : CheckedGeometry :=
  ⟨geometry00643, Geometry.check_of_directTraceCheck geometry00643
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00643 geometryTraceB00643 (by decide +kernel)⟩

def checkedGeometry00644 : CheckedGeometry :=
  ⟨geometry00644, Geometry.check_of_directTraceCheck geometry00644
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00644 geometryTraceB00644 (by decide +kernel)⟩

def checkedGeometry00645 : CheckedGeometry :=
  ⟨geometry00645, Geometry.check_of_directTraceCheck geometry00645
    checkedPatchCache0486 checkedPatchCache0487
    geometryTraceA00645 geometryTraceB00645 (by decide +kernel)⟩

def checkedGeometry00646 : CheckedGeometry :=
  ⟨geometry00646, Geometry.check_of_directTraceCheck geometry00646
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00646 geometryTraceB00646 (by decide +kernel)⟩

def checkedGeometry00647 : CheckedGeometry :=
  ⟨geometry00647, Geometry.check_of_directTraceCheck geometry00647
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00647 geometryTraceB00647 (by decide +kernel)⟩

def checkedGeometry00648 : CheckedGeometry :=
  ⟨geometry00648, Geometry.check_of_directTraceCheck geometry00648
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00648 geometryTraceB00648 (by decide +kernel)⟩

def checkedGeometry00649 : CheckedGeometry :=
  ⟨geometry00649, Geometry.check_of_directTraceCheck geometry00649
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00649 geometryTraceB00649 (by decide +kernel)⟩

def checkedGeometry00650 : CheckedGeometry :=
  ⟨geometry00650, Geometry.check_of_directTraceCheck geometry00650
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00650 geometryTraceB00650 (by decide +kernel)⟩

def checkedGeometry00651 : CheckedGeometry :=
  ⟨geometry00651, Geometry.check_of_directTraceCheck geometry00651
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00651 geometryTraceB00651 (by decide +kernel)⟩

def checkedGeometry00652 : CheckedGeometry :=
  ⟨geometry00652, Geometry.check_of_directTraceCheck geometry00652
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00652 geometryTraceB00652 (by decide +kernel)⟩

def checkedGeometry00653 : CheckedGeometry :=
  ⟨geometry00653, Geometry.check_of_directTraceCheck geometry00653
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00653 geometryTraceB00653 (by decide +kernel)⟩

def checkedGeometry00654 : CheckedGeometry :=
  ⟨geometry00654, Geometry.check_of_directTraceCheck geometry00654
    checkedPatchCache0488 checkedPatchCache0489
    geometryTraceA00654 geometryTraceB00654 (by decide +kernel)⟩

def checkedGeometry00655 : CheckedGeometry :=
  ⟨geometry00655, Geometry.check_of_directTraceCheck geometry00655
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00655 geometryTraceB00655 (by decide +kernel)⟩

def checkedGeometry00656 : CheckedGeometry :=
  ⟨geometry00656, Geometry.check_of_directTraceCheck geometry00656
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00656 geometryTraceB00656 (by decide +kernel)⟩

def checkedGeometry00657 : CheckedGeometry :=
  ⟨geometry00657, Geometry.check_of_directTraceCheck geometry00657
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00657 geometryTraceB00657 (by decide +kernel)⟩

def checkedGeometry00658 : CheckedGeometry :=
  ⟨geometry00658, Geometry.check_of_directTraceCheck geometry00658
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00658 geometryTraceB00658 (by decide +kernel)⟩

def checkedGeometry00659 : CheckedGeometry :=
  ⟨geometry00659, Geometry.check_of_directTraceCheck geometry00659
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00659 geometryTraceB00659 (by decide +kernel)⟩

def checkedGeometry00660 : CheckedGeometry :=
  ⟨geometry00660, Geometry.check_of_directTraceCheck geometry00660
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00660 geometryTraceB00660 (by decide +kernel)⟩

def checkedGeometry00661 : CheckedGeometry :=
  ⟨geometry00661, Geometry.check_of_directTraceCheck geometry00661
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00661 geometryTraceB00661 (by decide +kernel)⟩

def checkedGeometry00662 : CheckedGeometry :=
  ⟨geometry00662, Geometry.check_of_directTraceCheck geometry00662
    checkedPatchCache0490 checkedPatchCache0491
    geometryTraceA00662 geometryTraceB00662 (by decide +kernel)⟩

def checkedGeometry00663 : CheckedGeometry :=
  ⟨geometry00663, Geometry.check_of_directTraceCheck geometry00663
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00663 geometryTraceB00663 (by decide +kernel)⟩

def checkedGeometry00664 : CheckedGeometry :=
  ⟨geometry00664, Geometry.check_of_directTraceCheck geometry00664
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00664 geometryTraceB00664 (by decide +kernel)⟩

def checkedGeometry00665 : CheckedGeometry :=
  ⟨geometry00665, Geometry.check_of_directTraceCheck geometry00665
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00665 geometryTraceB00665 (by decide +kernel)⟩

def checkedGeometry00666 : CheckedGeometry :=
  ⟨geometry00666, Geometry.check_of_directTraceCheck geometry00666
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00666 geometryTraceB00666 (by decide +kernel)⟩

def checkedGeometry00667 : CheckedGeometry :=
  ⟨geometry00667, Geometry.check_of_directTraceCheck geometry00667
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00667 geometryTraceB00667 (by decide +kernel)⟩

def checkedGeometry00668 : CheckedGeometry :=
  ⟨geometry00668, Geometry.check_of_directTraceCheck geometry00668
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00668 geometryTraceB00668 (by decide +kernel)⟩

def checkedGeometry00669 : CheckedGeometry :=
  ⟨geometry00669, Geometry.check_of_directTraceCheck geometry00669
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00669 geometryTraceB00669 (by decide +kernel)⟩

def checkedGeometry00670 : CheckedGeometry :=
  ⟨geometry00670, Geometry.check_of_directTraceCheck geometry00670
    checkedPatchCache0492 checkedPatchCache0493
    geometryTraceA00670 geometryTraceB00670 (by decide +kernel)⟩

def checkedGeometry00671 : CheckedGeometry :=
  ⟨geometry00671, Geometry.check_of_directTraceCheck geometry00671
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00671 geometryTraceB00671 (by decide +kernel)⟩

def checkedGeometry00672 : CheckedGeometry :=
  ⟨geometry00672, Geometry.check_of_directTraceCheck geometry00672
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00672 geometryTraceB00672 (by decide +kernel)⟩

def checkedGeometry00673 : CheckedGeometry :=
  ⟨geometry00673, Geometry.check_of_directTraceCheck geometry00673
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00673 geometryTraceB00673 (by decide +kernel)⟩

def checkedGeometry00674 : CheckedGeometry :=
  ⟨geometry00674, Geometry.check_of_directTraceCheck geometry00674
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00674 geometryTraceB00674 (by decide +kernel)⟩

def checkedGeometry00675 : CheckedGeometry :=
  ⟨geometry00675, Geometry.check_of_directTraceCheck geometry00675
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00675 geometryTraceB00675 (by decide +kernel)⟩

def checkedGeometry00676 : CheckedGeometry :=
  ⟨geometry00676, Geometry.check_of_directTraceCheck geometry00676
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00676 geometryTraceB00676 (by decide +kernel)⟩

def checkedGeometry00677 : CheckedGeometry :=
  ⟨geometry00677, Geometry.check_of_directTraceCheck geometry00677
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00677 geometryTraceB00677 (by decide +kernel)⟩

def checkedGeometry00678 : CheckedGeometry :=
  ⟨geometry00678, Geometry.check_of_directTraceCheck geometry00678
    checkedPatchCache0494 checkedPatchCache0495
    geometryTraceA00678 geometryTraceB00678 (by decide +kernel)⟩

def checkedGeometry00679 : CheckedGeometry :=
  ⟨geometry00679, Geometry.check_of_directTraceCheck geometry00679
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00679 geometryTraceB00679 (by decide +kernel)⟩

def checkedGeometry00680 : CheckedGeometry :=
  ⟨geometry00680, Geometry.check_of_directTraceCheck geometry00680
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00680 geometryTraceB00680 (by decide +kernel)⟩

def checkedGeometry00681 : CheckedGeometry :=
  ⟨geometry00681, Geometry.check_of_directTraceCheck geometry00681
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00681 geometryTraceB00681 (by decide +kernel)⟩

def checkedGeometry00682 : CheckedGeometry :=
  ⟨geometry00682, Geometry.check_of_directTraceCheck geometry00682
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00682 geometryTraceB00682 (by decide +kernel)⟩

def checkedGeometry00683 : CheckedGeometry :=
  ⟨geometry00683, Geometry.check_of_directTraceCheck geometry00683
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00683 geometryTraceB00683 (by decide +kernel)⟩

def checkedGeometry00684 : CheckedGeometry :=
  ⟨geometry00684, Geometry.check_of_directTraceCheck geometry00684
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00684 geometryTraceB00684 (by decide +kernel)⟩

def checkedGeometry00685 : CheckedGeometry :=
  ⟨geometry00685, Geometry.check_of_directTraceCheck geometry00685
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00685 geometryTraceB00685 (by decide +kernel)⟩

def checkedGeometry00686 : CheckedGeometry :=
  ⟨geometry00686, Geometry.check_of_directTraceCheck geometry00686
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00686 geometryTraceB00686 (by decide +kernel)⟩

def checkedGeometry00687 : CheckedGeometry :=
  ⟨geometry00687, Geometry.check_of_directTraceCheck geometry00687
    checkedPatchCache0496 checkedPatchCache0497
    geometryTraceA00687 geometryTraceB00687 (by decide +kernel)⟩

def checkedGeometry00688 : CheckedGeometry :=
  ⟨geometry00688, Geometry.check_of_directTraceCheck geometry00688
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00688 geometryTraceB00688 (by decide +kernel)⟩

def checkedGeometry00689 : CheckedGeometry :=
  ⟨geometry00689, Geometry.check_of_directTraceCheck geometry00689
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00689 geometryTraceB00689 (by decide +kernel)⟩

def checkedGeometry00690 : CheckedGeometry :=
  ⟨geometry00690, Geometry.check_of_directTraceCheck geometry00690
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00690 geometryTraceB00690 (by decide +kernel)⟩

def checkedGeometry00691 : CheckedGeometry :=
  ⟨geometry00691, Geometry.check_of_directTraceCheck geometry00691
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00691 geometryTraceB00691 (by decide +kernel)⟩

def checkedGeometry00692 : CheckedGeometry :=
  ⟨geometry00692, Geometry.check_of_directTraceCheck geometry00692
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00692 geometryTraceB00692 (by decide +kernel)⟩

def checkedGeometry00693 : CheckedGeometry :=
  ⟨geometry00693, Geometry.check_of_directTraceCheck geometry00693
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00693 geometryTraceB00693 (by decide +kernel)⟩

def checkedGeometry00694 : CheckedGeometry :=
  ⟨geometry00694, Geometry.check_of_directTraceCheck geometry00694
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00694 geometryTraceB00694 (by decide +kernel)⟩

def checkedGeometry00695 : CheckedGeometry :=
  ⟨geometry00695, Geometry.check_of_directTraceCheck geometry00695
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00695 geometryTraceB00695 (by decide +kernel)⟩

def checkedGeometry00696 : CheckedGeometry :=
  ⟨geometry00696, Geometry.check_of_directTraceCheck geometry00696
    checkedPatchCache0498 checkedPatchCache0499
    geometryTraceA00696 geometryTraceB00696 (by decide +kernel)⟩

def checkedGeometry00697 : CheckedGeometry :=
  ⟨geometry00697, Geometry.check_of_directTraceCheck geometry00697
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00697 geometryTraceB00697 (by decide +kernel)⟩

def checkedGeometry00698 : CheckedGeometry :=
  ⟨geometry00698, Geometry.check_of_directTraceCheck geometry00698
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00698 geometryTraceB00698 (by decide +kernel)⟩

def checkedGeometry00699 : CheckedGeometry :=
  ⟨geometry00699, Geometry.check_of_directTraceCheck geometry00699
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00699 geometryTraceB00699 (by decide +kernel)⟩

def checkedGeometry00700 : CheckedGeometry :=
  ⟨geometry00700, Geometry.check_of_directTraceCheck geometry00700
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00700 geometryTraceB00700 (by decide +kernel)⟩

def checkedGeometry00701 : CheckedGeometry :=
  ⟨geometry00701, Geometry.check_of_directTraceCheck geometry00701
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00701 geometryTraceB00701 (by decide +kernel)⟩

def checkedGeometry00702 : CheckedGeometry :=
  ⟨geometry00702, Geometry.check_of_directTraceCheck geometry00702
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00702 geometryTraceB00702 (by decide +kernel)⟩

def checkedGeometry00703 : CheckedGeometry :=
  ⟨geometry00703, Geometry.check_of_directTraceCheck geometry00703
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00703 geometryTraceB00703 (by decide +kernel)⟩

def checkedGeometry00704 : CheckedGeometry :=
  ⟨geometry00704, Geometry.check_of_directTraceCheck geometry00704
    checkedPatchCache0500 checkedPatchCache0501
    geometryTraceA00704 geometryTraceB00704 (by decide +kernel)⟩

def checkedGeometry00705 : CheckedGeometry :=
  ⟨geometry00705, Geometry.check_of_directTraceCheck geometry00705
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00705 geometryTraceB00705 (by decide +kernel)⟩

def checkedGeometry00706 : CheckedGeometry :=
  ⟨geometry00706, Geometry.check_of_directTraceCheck geometry00706
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00706 geometryTraceB00706 (by decide +kernel)⟩

def checkedGeometry00707 : CheckedGeometry :=
  ⟨geometry00707, Geometry.check_of_directTraceCheck geometry00707
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00707 geometryTraceB00707 (by decide +kernel)⟩

def checkedGeometry00708 : CheckedGeometry :=
  ⟨geometry00708, Geometry.check_of_directTraceCheck geometry00708
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00708 geometryTraceB00708 (by decide +kernel)⟩

def checkedGeometry00709 : CheckedGeometry :=
  ⟨geometry00709, Geometry.check_of_directTraceCheck geometry00709
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00709 geometryTraceB00709 (by decide +kernel)⟩

def checkedGeometry00710 : CheckedGeometry :=
  ⟨geometry00710, Geometry.check_of_directTraceCheck geometry00710
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00710 geometryTraceB00710 (by decide +kernel)⟩

def checkedGeometry00711 : CheckedGeometry :=
  ⟨geometry00711, Geometry.check_of_directTraceCheck geometry00711
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00711 geometryTraceB00711 (by decide +kernel)⟩

def checkedGeometry00712 : CheckedGeometry :=
  ⟨geometry00712, Geometry.check_of_directTraceCheck geometry00712
    checkedPatchCache0502 checkedPatchCache0503
    geometryTraceA00712 geometryTraceB00712 (by decide +kernel)⟩

def checkedGeometry00713 : CheckedGeometry :=
  ⟨geometry00713, Geometry.check_of_directTraceCheck geometry00713
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00713 geometryTraceB00713 (by decide +kernel)⟩

def checkedGeometry00714 : CheckedGeometry :=
  ⟨geometry00714, Geometry.check_of_directTraceCheck geometry00714
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00714 geometryTraceB00714 (by decide +kernel)⟩

def checkedGeometry00715 : CheckedGeometry :=
  ⟨geometry00715, Geometry.check_of_directTraceCheck geometry00715
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00715 geometryTraceB00715 (by decide +kernel)⟩

def checkedGeometry00716 : CheckedGeometry :=
  ⟨geometry00716, Geometry.check_of_directTraceCheck geometry00716
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00716 geometryTraceB00716 (by decide +kernel)⟩

def checkedGeometry00717 : CheckedGeometry :=
  ⟨geometry00717, Geometry.check_of_directTraceCheck geometry00717
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00717 geometryTraceB00717 (by decide +kernel)⟩

def checkedGeometry00718 : CheckedGeometry :=
  ⟨geometry00718, Geometry.check_of_directTraceCheck geometry00718
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00718 geometryTraceB00718 (by decide +kernel)⟩

def checkedGeometry00719 : CheckedGeometry :=
  ⟨geometry00719, Geometry.check_of_directTraceCheck geometry00719
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00719 geometryTraceB00719 (by decide +kernel)⟩

def checkedGeometry00720 : CheckedGeometry :=
  ⟨geometry00720, Geometry.check_of_directTraceCheck geometry00720
    checkedPatchCache0504 checkedPatchCache0505
    geometryTraceA00720 geometryTraceB00720 (by decide +kernel)⟩

def checkedGeometry00721 : CheckedGeometry :=
  ⟨geometry00721, Geometry.check_of_directTraceCheck geometry00721
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00721 geometryTraceB00721 (by decide +kernel)⟩

def checkedGeometry00722 : CheckedGeometry :=
  ⟨geometry00722, Geometry.check_of_directTraceCheck geometry00722
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00722 geometryTraceB00722 (by decide +kernel)⟩

def checkedGeometry00723 : CheckedGeometry :=
  ⟨geometry00723, Geometry.check_of_directTraceCheck geometry00723
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00723 geometryTraceB00723 (by decide +kernel)⟩

def checkedGeometry00724 : CheckedGeometry :=
  ⟨geometry00724, Geometry.check_of_directTraceCheck geometry00724
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00724 geometryTraceB00724 (by decide +kernel)⟩

def checkedGeometry00725 : CheckedGeometry :=
  ⟨geometry00725, Geometry.check_of_directTraceCheck geometry00725
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00725 geometryTraceB00725 (by decide +kernel)⟩

def checkedGeometry00726 : CheckedGeometry :=
  ⟨geometry00726, Geometry.check_of_directTraceCheck geometry00726
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00726 geometryTraceB00726 (by decide +kernel)⟩

def checkedGeometry00727 : CheckedGeometry :=
  ⟨geometry00727, Geometry.check_of_directTraceCheck geometry00727
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00727 geometryTraceB00727 (by decide +kernel)⟩

def checkedGeometry00728 : CheckedGeometry :=
  ⟨geometry00728, Geometry.check_of_directTraceCheck geometry00728
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00728 geometryTraceB00728 (by decide +kernel)⟩

def checkedGeometry00729 : CheckedGeometry :=
  ⟨geometry00729, Geometry.check_of_directTraceCheck geometry00729
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00729 geometryTraceB00729 (by decide +kernel)⟩

def checkedGeometry00730 : CheckedGeometry :=
  ⟨geometry00730, Geometry.check_of_directTraceCheck geometry00730
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00730 geometryTraceB00730 (by decide +kernel)⟩

def checkedGeometry00731 : CheckedGeometry :=
  ⟨geometry00731, Geometry.check_of_directTraceCheck geometry00731
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00731 geometryTraceB00731 (by decide +kernel)⟩

def checkedGeometry00732 : CheckedGeometry :=
  ⟨geometry00732, Geometry.check_of_directTraceCheck geometry00732
    checkedPatchCache0506 checkedPatchCache0507
    geometryTraceA00732 geometryTraceB00732 (by decide +kernel)⟩

def checkedGeometry00733 : CheckedGeometry :=
  ⟨geometry00733, Geometry.check_of_directTraceCheck geometry00733
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00733 geometryTraceB00733 (by decide +kernel)⟩

def checkedGeometry00734 : CheckedGeometry :=
  ⟨geometry00734, Geometry.check_of_directTraceCheck geometry00734
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00734 geometryTraceB00734 (by decide +kernel)⟩

def checkedGeometry00735 : CheckedGeometry :=
  ⟨geometry00735, Geometry.check_of_directTraceCheck geometry00735
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00735 geometryTraceB00735 (by decide +kernel)⟩

def checkedGeometry00736 : CheckedGeometry :=
  ⟨geometry00736, Geometry.check_of_directTraceCheck geometry00736
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00736 geometryTraceB00736 (by decide +kernel)⟩

def checkedGeometry00737 : CheckedGeometry :=
  ⟨geometry00737, Geometry.check_of_directTraceCheck geometry00737
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00737 geometryTraceB00737 (by decide +kernel)⟩

def checkedGeometry00738 : CheckedGeometry :=
  ⟨geometry00738, Geometry.check_of_directTraceCheck geometry00738
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00738 geometryTraceB00738 (by decide +kernel)⟩

def checkedGeometry00739 : CheckedGeometry :=
  ⟨geometry00739, Geometry.check_of_directTraceCheck geometry00739
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00739 geometryTraceB00739 (by decide +kernel)⟩

def checkedGeometry00740 : CheckedGeometry :=
  ⟨geometry00740, Geometry.check_of_directTraceCheck geometry00740
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00740 geometryTraceB00740 (by decide +kernel)⟩

def checkedGeometry00741 : CheckedGeometry :=
  ⟨geometry00741, Geometry.check_of_directTraceCheck geometry00741
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00741 geometryTraceB00741 (by decide +kernel)⟩

def checkedGeometry00742 : CheckedGeometry :=
  ⟨geometry00742, Geometry.check_of_directTraceCheck geometry00742
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00742 geometryTraceB00742 (by decide +kernel)⟩

def checkedGeometry00743 : CheckedGeometry :=
  ⟨geometry00743, Geometry.check_of_directTraceCheck geometry00743
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00743 geometryTraceB00743 (by decide +kernel)⟩

def checkedGeometry00744 : CheckedGeometry :=
  ⟨geometry00744, Geometry.check_of_directTraceCheck geometry00744
    checkedPatchCache0508 checkedPatchCache0509
    geometryTraceA00744 geometryTraceB00744 (by decide +kernel)⟩

def checkedGeometry00745 : CheckedGeometry :=
  ⟨geometry00745, Geometry.check_of_directTraceCheck geometry00745
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00745 geometryTraceB00745 (by decide +kernel)⟩

def checkedGeometry00746 : CheckedGeometry :=
  ⟨geometry00746, Geometry.check_of_directTraceCheck geometry00746
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00746 geometryTraceB00746 (by decide +kernel)⟩

def checkedGeometry00747 : CheckedGeometry :=
  ⟨geometry00747, Geometry.check_of_directTraceCheck geometry00747
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00747 geometryTraceB00747 (by decide +kernel)⟩

def checkedGeometry00748 : CheckedGeometry :=
  ⟨geometry00748, Geometry.check_of_directTraceCheck geometry00748
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00748 geometryTraceB00748 (by decide +kernel)⟩

def checkedGeometry00749 : CheckedGeometry :=
  ⟨geometry00749, Geometry.check_of_directTraceCheck geometry00749
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00749 geometryTraceB00749 (by decide +kernel)⟩

def checkedGeometry00750 : CheckedGeometry :=
  ⟨geometry00750, Geometry.check_of_directTraceCheck geometry00750
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00750 geometryTraceB00750 (by decide +kernel)⟩

def checkedGeometry00751 : CheckedGeometry :=
  ⟨geometry00751, Geometry.check_of_directTraceCheck geometry00751
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00751 geometryTraceB00751 (by decide +kernel)⟩

def checkedGeometry00752 : CheckedGeometry :=
  ⟨geometry00752, Geometry.check_of_directTraceCheck geometry00752
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00752 geometryTraceB00752 (by decide +kernel)⟩

def checkedGeometry00753 : CheckedGeometry :=
  ⟨geometry00753, Geometry.check_of_directTraceCheck geometry00753
    checkedPatchCache0510 checkedPatchCache0511
    geometryTraceA00753 geometryTraceB00753 (by decide +kernel)⟩

def checkedGeometry00754 : CheckedGeometry :=
  ⟨geometry00754, Geometry.check_of_directTraceCheck geometry00754
    checkedPatchCache0512 checkedPatchCache0513
    geometryTraceA00754 geometryTraceB00754 (by decide +kernel)⟩

def checkedGeometry00755 : CheckedGeometry :=
  ⟨geometry00755, Geometry.check_of_directTraceCheck geometry00755
    checkedPatchCache0514 checkedPatchCache0515
    geometryTraceA00755 geometryTraceB00755 (by decide +kernel)⟩

def checkedGeometry00756 : CheckedGeometry :=
  ⟨geometry00756, Geometry.check_of_directTraceCheck geometry00756
    checkedPatchCache0516 checkedPatchCache0517
    geometryTraceA00756 geometryTraceB00756 (by decide +kernel)⟩

def checkedGeometry00757 : CheckedGeometry :=
  ⟨geometry00757, Geometry.check_of_directTraceCheck geometry00757
    checkedPatchCache0518 checkedPatchCache0519
    geometryTraceA00757 geometryTraceB00757 (by decide +kernel)⟩

def checkedGeometry00758 : CheckedGeometry :=
  ⟨geometry00758, Geometry.check_of_directTraceCheck geometry00758
    checkedPatchCache0520 checkedPatchCache0521
    geometryTraceA00758 geometryTraceB00758 (by decide +kernel)⟩

def checkedGeometry00759 : CheckedGeometry :=
  ⟨geometry00759, Geometry.check_of_directTraceCheck geometry00759
    checkedPatchCache0522 checkedPatchCache0523
    geometryTraceA00759 geometryTraceB00759 (by decide +kernel)⟩

def checkedGeometry00760 : CheckedGeometry :=
  ⟨geometry00760, Geometry.check_of_directTraceCheck geometry00760
    checkedPatchCache0524 checkedPatchCache0525
    geometryTraceA00760 geometryTraceB00760 (by decide +kernel)⟩

def checkedGeometry00761 : CheckedGeometry :=
  ⟨geometry00761, Geometry.check_of_directTraceCheck geometry00761
    checkedPatchCache0526 checkedPatchCache0527
    geometryTraceA00761 geometryTraceB00761 (by decide +kernel)⟩

def checkedGeometry00762 : CheckedGeometry :=
  ⟨geometry00762, Geometry.check_of_directTraceCheck geometry00762
    checkedPatchCache0528 checkedPatchCache0529
    geometryTraceA00762 geometryTraceB00762 (by decide +kernel)⟩

def checkedGeometry00763 : CheckedGeometry :=
  ⟨geometry00763, Geometry.check_of_directTraceCheck geometry00763
    checkedPatchCache0530 checkedPatchCache0531
    geometryTraceA00763 geometryTraceB00763 (by decide +kernel)⟩

def checkedGeometry00764 : CheckedGeometry :=
  ⟨geometry00764, Geometry.check_of_directTraceCheck geometry00764
    checkedPatchCache0532 checkedPatchCache0533
    geometryTraceA00764 geometryTraceB00764 (by decide +kernel)⟩

def checkedGeometry00765 : CheckedGeometry :=
  ⟨geometry00765, Geometry.check_of_directTraceCheck geometry00765
    checkedPatchCache0534 checkedPatchCache0535
    geometryTraceA00765 geometryTraceB00765 (by decide +kernel)⟩

def checkedGeometry00766 : CheckedGeometry :=
  ⟨geometry00766, Geometry.check_of_directTraceCheck geometry00766
    checkedPatchCache0536 checkedPatchCache0537
    geometryTraceA00766 geometryTraceB00766 (by decide +kernel)⟩

def checkedGeometry00767 : CheckedGeometry :=
  ⟨geometry00767, Geometry.check_of_directTraceCheck geometry00767
    checkedPatchCache0538 checkedPatchCache0539
    geometryTraceA00767 geometryTraceB00767 (by decide +kernel)⟩


end
end ErdosOverlap.Native6Leaves
