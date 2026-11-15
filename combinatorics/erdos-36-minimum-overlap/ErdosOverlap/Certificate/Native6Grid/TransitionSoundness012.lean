/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck096
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck097
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck098
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck099
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck100
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck101
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck102
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck103

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk012 (j : ℕ) (hlo : 768 ≤ j) (hhi : j < 832) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0768
  · exact transition0769
  · exact transition0770
  · exact transition0771
  · exact transition0772
  · exact transition0773
  · exact transition0774
  · exact transition0775
  · exact transition0776
  · exact transition0777
  · exact transition0778
  · exact transition0779
  · exact transition0780
  · exact transition0781
  · exact transition0782
  · exact transition0783
  · exact transition0784
  · exact transition0785
  · exact transition0786
  · exact transition0787
  · exact transition0788
  · exact transition0789
  · exact transition0790
  · exact transition0791
  · exact transition0792
  · exact transition0793
  · exact transition0794
  · exact transition0795
  · exact transition0796
  · exact transition0797
  · exact transition0798
  · exact transition0799
  · exact transition0800
  · exact transition0801
  · exact transition0802
  · exact transition0803
  · exact transition0804
  · exact transition0805
  · exact transition0806
  · exact transition0807
  · exact transition0808
  · exact transition0809
  · exact transition0810
  · exact transition0811
  · exact transition0812
  · exact transition0813
  · exact transition0814
  · exact transition0815
  · exact transition0816
  · exact transition0817
  · exact transition0818
  · exact transition0819
  · exact transition0820
  · exact transition0821
  · exact transition0822
  · exact transition0823
  · exact transition0824
  · exact transition0825
  · exact transition0826
  · exact transition0827
  · exact transition0828
  · exact transition0829
  · exact transition0830
  · exact transition0831

end
end ErdosOverlap.Native6Grid
