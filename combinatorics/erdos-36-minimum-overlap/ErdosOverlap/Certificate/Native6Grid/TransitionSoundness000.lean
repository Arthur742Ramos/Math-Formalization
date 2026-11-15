/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck000
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck001
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck002
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck003
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck004
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck005
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck006
public import ErdosOverlap.Certificate.Native6Grid.TransitionCheck007

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transitions_chunk000 (j : ℕ) (hlo : 0 ≤ j) (hhi : j < 64) :
    transitionRowCheck seeds (stateRow j) (stateRow (j + 1)) = true := by
  interval_cases j
  · exact transition0000
  · exact transition0001
  · exact transition0002
  · exact transition0003
  · exact transition0004
  · exact transition0005
  · exact transition0006
  · exact transition0007
  · exact transition0008
  · exact transition0009
  · exact transition0010
  · exact transition0011
  · exact transition0012
  · exact transition0013
  · exact transition0014
  · exact transition0015
  · exact transition0016
  · exact transition0017
  · exact transition0018
  · exact transition0019
  · exact transition0020
  · exact transition0021
  · exact transition0022
  · exact transition0023
  · exact transition0024
  · exact transition0025
  · exact transition0026
  · exact transition0027
  · exact transition0028
  · exact transition0029
  · exact transition0030
  · exact transition0031
  · exact transition0032
  · exact transition0033
  · exact transition0034
  · exact transition0035
  · exact transition0036
  · exact transition0037
  · exact transition0038
  · exact transition0039
  · exact transition0040
  · exact transition0041
  · exact transition0042
  · exact transition0043
  · exact transition0044
  · exact transition0045
  · exact transition0046
  · exact transition0047
  · exact transition0048
  · exact transition0049
  · exact transition0050
  · exact transition0051
  · exact transition0052
  · exact transition0053
  · exact transition0054
  · exact transition0055
  · exact transition0056
  · exact transition0057
  · exact transition0058
  · exact transition0059
  · exact transition0060
  · exact transition0061
  · exact transition0062
  · exact transition0063

end
end ErdosOverlap.Native6Grid
