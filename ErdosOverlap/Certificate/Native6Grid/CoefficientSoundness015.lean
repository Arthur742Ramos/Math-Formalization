/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck120
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck121
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck122
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck123
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck124
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck125
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck126
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck127

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk015 (j : ℕ) (hlo : 960 ≤ j) (hhi : j < 1024) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0960
  · exact coefficientCheck0961
  · exact coefficientCheck0962
  · exact coefficientCheck0963
  · exact coefficientCheck0964
  · exact coefficientCheck0965
  · exact coefficientCheck0966
  · exact coefficientCheck0967
  · exact coefficientCheck0968
  · exact coefficientCheck0969
  · exact coefficientCheck0970
  · exact coefficientCheck0971
  · exact coefficientCheck0972
  · exact coefficientCheck0973
  · exact coefficientCheck0974
  · exact coefficientCheck0975
  · exact coefficientCheck0976
  · exact coefficientCheck0977
  · exact coefficientCheck0978
  · exact coefficientCheck0979
  · exact coefficientCheck0980
  · exact coefficientCheck0981
  · exact coefficientCheck0982
  · exact coefficientCheck0983
  · exact coefficientCheck0984
  · exact coefficientCheck0985
  · exact coefficientCheck0986
  · exact coefficientCheck0987
  · exact coefficientCheck0988
  · exact coefficientCheck0989
  · exact coefficientCheck0990
  · exact coefficientCheck0991
  · exact coefficientCheck0992
  · exact coefficientCheck0993
  · exact coefficientCheck0994
  · exact coefficientCheck0995
  · exact coefficientCheck0996
  · exact coefficientCheck0997
  · exact coefficientCheck0998
  · exact coefficientCheck0999
  · exact coefficientCheck1000
  · exact coefficientCheck1001
  · exact coefficientCheck1002
  · exact coefficientCheck1003
  · exact coefficientCheck1004
  · exact coefficientCheck1005
  · exact coefficientCheck1006
  · exact coefficientCheck1007
  · exact coefficientCheck1008
  · exact coefficientCheck1009
  · exact coefficientCheck1010
  · exact coefficientCheck1011
  · exact coefficientCheck1012
  · exact coefficientCheck1013
  · exact coefficientCheck1014
  · exact coefficientCheck1015
  · exact coefficientCheck1016
  · exact coefficientCheck1017
  · exact coefficientCheck1018
  · exact coefficientCheck1019
  · exact coefficientCheck1020
  · exact coefficientCheck1021
  · exact coefficientCheck1022
  · exact coefficientCheck1023

end
end ErdosOverlap.Native6Grid
