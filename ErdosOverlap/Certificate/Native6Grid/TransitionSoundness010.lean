/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck080
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck081
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck082
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck083
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck084
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck085
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck086
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck087

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk010 (j : ℕ) (hlo : 640 ≤ j) (hhi : j < 704) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0640
  · exact transition0641
  · exact transition0642
  · exact transition0643
  · exact transition0644
  · exact transition0645
  · exact transition0646
  · exact transition0647
  · exact transition0648
  · exact transition0649
  · exact transition0650
  · exact transition0651
  · exact transition0652
  · exact transition0653
  · exact transition0654
  · exact transition0655
  · exact transition0656
  · exact transition0657
  · exact transition0658
  · exact transition0659
  · exact transition0660
  · exact transition0661
  · exact transition0662
  · exact transition0663
  · exact transition0664
  · exact transition0665
  · exact transition0666
  · exact transition0667
  · exact transition0668
  · exact transition0669
  · exact transition0670
  · exact transition0671
  · exact transition0672
  · exact transition0673
  · exact transition0674
  · exact transition0675
  · exact transition0676
  · exact transition0677
  · exact transition0678
  · exact transition0679
  · exact transition0680
  · exact transition0681
  · exact transition0682
  · exact transition0683
  · exact transition0684
  · exact transition0685
  · exact transition0686
  · exact transition0687
  · exact transition0688
  · exact transition0689
  · exact transition0690
  · exact transition0691
  · exact transition0692
  · exact transition0693
  · exact transition0694
  · exact transition0695
  · exact transition0696
  · exact transition0697
  · exact transition0698
  · exact transition0699
  · exact transition0700
  · exact transition0701
  · exact transition0702
  · exact transition0703

end
end ErdosOverlap.Native6Grid
