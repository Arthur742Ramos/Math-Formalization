/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck072
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck073
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck074
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck075
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck076
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck077
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck078
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck079

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk009 (j : ℕ) (hlo : 576 ≤ j) (hhi : j < 640) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0576
  · exact transition0577
  · exact transition0578
  · exact transition0579
  · exact transition0580
  · exact transition0581
  · exact transition0582
  · exact transition0583
  · exact transition0584
  · exact transition0585
  · exact transition0586
  · exact transition0587
  · exact transition0588
  · exact transition0589
  · exact transition0590
  · exact transition0591
  · exact transition0592
  · exact transition0593
  · exact transition0594
  · exact transition0595
  · exact transition0596
  · exact transition0597
  · exact transition0598
  · exact transition0599
  · exact transition0600
  · exact transition0601
  · exact transition0602
  · exact transition0603
  · exact transition0604
  · exact transition0605
  · exact transition0606
  · exact transition0607
  · exact transition0608
  · exact transition0609
  · exact transition0610
  · exact transition0611
  · exact transition0612
  · exact transition0613
  · exact transition0614
  · exact transition0615
  · exact transition0616
  · exact transition0617
  · exact transition0618
  · exact transition0619
  · exact transition0620
  · exact transition0621
  · exact transition0622
  · exact transition0623
  · exact transition0624
  · exact transition0625
  · exact transition0626
  · exact transition0627
  · exact transition0628
  · exact transition0629
  · exact transition0630
  · exact transition0631
  · exact transition0632
  · exact transition0633
  · exact transition0634
  · exact transition0635
  · exact transition0636
  · exact transition0637
  · exact transition0638
  · exact transition0639

end
end ErdosOverlap.Native6Grid
