/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck104
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck105
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck106
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck107
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck108
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck109
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck110
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck111

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk013 (j : ℕ) (hlo : 832 ≤ j) (hhi : j < 896) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0832
  · exact transition0833
  · exact transition0834
  · exact transition0835
  · exact transition0836
  · exact transition0837
  · exact transition0838
  · exact transition0839
  · exact transition0840
  · exact transition0841
  · exact transition0842
  · exact transition0843
  · exact transition0844
  · exact transition0845
  · exact transition0846
  · exact transition0847
  · exact transition0848
  · exact transition0849
  · exact transition0850
  · exact transition0851
  · exact transition0852
  · exact transition0853
  · exact transition0854
  · exact transition0855
  · exact transition0856
  · exact transition0857
  · exact transition0858
  · exact transition0859
  · exact transition0860
  · exact transition0861
  · exact transition0862
  · exact transition0863
  · exact transition0864
  · exact transition0865
  · exact transition0866
  · exact transition0867
  · exact transition0868
  · exact transition0869
  · exact transition0870
  · exact transition0871
  · exact transition0872
  · exact transition0873
  · exact transition0874
  · exact transition0875
  · exact transition0876
  · exact transition0877
  · exact transition0878
  · exact transition0879
  · exact transition0880
  · exact transition0881
  · exact transition0882
  · exact transition0883
  · exact transition0884
  · exact transition0885
  · exact transition0886
  · exact transition0887
  · exact transition0888
  · exact transition0889
  · exact transition0890
  · exact transition0891
  · exact transition0892
  · exact transition0893
  · exact transition0894
  · exact transition0895

end
end ErdosOverlap.Native6Grid
