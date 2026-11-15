/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck120
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck121
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck122
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck123
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck124
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck125
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck126
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck127

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk015 (j : ℕ) (hlo : 960 ≤ j) (hhi : j < 1023) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0960
  · exact transition0961
  · exact transition0962
  · exact transition0963
  · exact transition0964
  · exact transition0965
  · exact transition0966
  · exact transition0967
  · exact transition0968
  · exact transition0969
  · exact transition0970
  · exact transition0971
  · exact transition0972
  · exact transition0973
  · exact transition0974
  · exact transition0975
  · exact transition0976
  · exact transition0977
  · exact transition0978
  · exact transition0979
  · exact transition0980
  · exact transition0981
  · exact transition0982
  · exact transition0983
  · exact transition0984
  · exact transition0985
  · exact transition0986
  · exact transition0987
  · exact transition0988
  · exact transition0989
  · exact transition0990
  · exact transition0991
  · exact transition0992
  · exact transition0993
  · exact transition0994
  · exact transition0995
  · exact transition0996
  · exact transition0997
  · exact transition0998
  · exact transition0999
  · exact transition1000
  · exact transition1001
  · exact transition1002
  · exact transition1003
  · exact transition1004
  · exact transition1005
  · exact transition1006
  · exact transition1007
  · exact transition1008
  · exact transition1009
  · exact transition1010
  · exact transition1011
  · exact transition1012
  · exact transition1013
  · exact transition1014
  · exact transition1015
  · exact transition1016
  · exact transition1017
  · exact transition1018
  · exact transition1019
  · exact transition1020
  · exact transition1021
  · exact transition1022

end
end ErdosOverlap.Native6Grid
