/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck112
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck113
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck114
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck115
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck116
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck117
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck118
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck119

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk014 (j : ℕ) (hlo : 896 ≤ j) (hhi : j < 960) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0896
  · exact transition0897
  · exact transition0898
  · exact transition0899
  · exact transition0900
  · exact transition0901
  · exact transition0902
  · exact transition0903
  · exact transition0904
  · exact transition0905
  · exact transition0906
  · exact transition0907
  · exact transition0908
  · exact transition0909
  · exact transition0910
  · exact transition0911
  · exact transition0912
  · exact transition0913
  · exact transition0914
  · exact transition0915
  · exact transition0916
  · exact transition0917
  · exact transition0918
  · exact transition0919
  · exact transition0920
  · exact transition0921
  · exact transition0922
  · exact transition0923
  · exact transition0924
  · exact transition0925
  · exact transition0926
  · exact transition0927
  · exact transition0928
  · exact transition0929
  · exact transition0930
  · exact transition0931
  · exact transition0932
  · exact transition0933
  · exact transition0934
  · exact transition0935
  · exact transition0936
  · exact transition0937
  · exact transition0938
  · exact transition0939
  · exact transition0940
  · exact transition0941
  · exact transition0942
  · exact transition0943
  · exact transition0944
  · exact transition0945
  · exact transition0946
  · exact transition0947
  · exact transition0948
  · exact transition0949
  · exact transition0950
  · exact transition0951
  · exact transition0952
  · exact transition0953
  · exact transition0954
  · exact transition0955
  · exact transition0956
  · exact transition0957
  · exact transition0958
  · exact transition0959

end
end ErdosOverlap.Native6Grid
