/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck064
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck065
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck066
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck067
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck068
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck069
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck070
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck071

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk008 (j : ℕ) (hlo : 512 ≤ j) (hhi : j < 576) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0512
  · exact transition0513
  · exact transition0514
  · exact transition0515
  · exact transition0516
  · exact transition0517
  · exact transition0518
  · exact transition0519
  · exact transition0520
  · exact transition0521
  · exact transition0522
  · exact transition0523
  · exact transition0524
  · exact transition0525
  · exact transition0526
  · exact transition0527
  · exact transition0528
  · exact transition0529
  · exact transition0530
  · exact transition0531
  · exact transition0532
  · exact transition0533
  · exact transition0534
  · exact transition0535
  · exact transition0536
  · exact transition0537
  · exact transition0538
  · exact transition0539
  · exact transition0540
  · exact transition0541
  · exact transition0542
  · exact transition0543
  · exact transition0544
  · exact transition0545
  · exact transition0546
  · exact transition0547
  · exact transition0548
  · exact transition0549
  · exact transition0550
  · exact transition0551
  · exact transition0552
  · exact transition0553
  · exact transition0554
  · exact transition0555
  · exact transition0556
  · exact transition0557
  · exact transition0558
  · exact transition0559
  · exact transition0560
  · exact transition0561
  · exact transition0562
  · exact transition0563
  · exact transition0564
  · exact transition0565
  · exact transition0566
  · exact transition0567
  · exact transition0568
  · exact transition0569
  · exact transition0570
  · exact transition0571
  · exact transition0572
  · exact transition0573
  · exact transition0574
  · exact transition0575

end
end ErdosOverlap.Native6Grid
