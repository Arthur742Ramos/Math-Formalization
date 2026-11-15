/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck088
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck089
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck090
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck091
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck092
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck093
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck094
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck095

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk011 (j : ℕ) (hlo : 704 ≤ j) (hhi : j < 768) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0704
  · exact transition0705
  · exact transition0706
  · exact transition0707
  · exact transition0708
  · exact transition0709
  · exact transition0710
  · exact transition0711
  · exact transition0712
  · exact transition0713
  · exact transition0714
  · exact transition0715
  · exact transition0716
  · exact transition0717
  · exact transition0718
  · exact transition0719
  · exact transition0720
  · exact transition0721
  · exact transition0722
  · exact transition0723
  · exact transition0724
  · exact transition0725
  · exact transition0726
  · exact transition0727
  · exact transition0728
  · exact transition0729
  · exact transition0730
  · exact transition0731
  · exact transition0732
  · exact transition0733
  · exact transition0734
  · exact transition0735
  · exact transition0736
  · exact transition0737
  · exact transition0738
  · exact transition0739
  · exact transition0740
  · exact transition0741
  · exact transition0742
  · exact transition0743
  · exact transition0744
  · exact transition0745
  · exact transition0746
  · exact transition0747
  · exact transition0748
  · exact transition0749
  · exact transition0750
  · exact transition0751
  · exact transition0752
  · exact transition0753
  · exact transition0754
  · exact transition0755
  · exact transition0756
  · exact transition0757
  · exact transition0758
  · exact transition0759
  · exact transition0760
  · exact transition0761
  · exact transition0762
  · exact transition0763
  · exact transition0764
  · exact transition0765
  · exact transition0766
  · exact transition0767

end
end ErdosOverlap.Native6Grid
