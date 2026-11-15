/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck112
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck113
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck114
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck115
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck116
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck117
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck118
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck119

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk014 (j : ℕ) (hlo : 896 ≤ j) (hhi : j < 960) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0896
  · exact coefficientCheck0897
  · exact coefficientCheck0898
  · exact coefficientCheck0899
  · exact coefficientCheck0900
  · exact coefficientCheck0901
  · exact coefficientCheck0902
  · exact coefficientCheck0903
  · exact coefficientCheck0904
  · exact coefficientCheck0905
  · exact coefficientCheck0906
  · exact coefficientCheck0907
  · exact coefficientCheck0908
  · exact coefficientCheck0909
  · exact coefficientCheck0910
  · exact coefficientCheck0911
  · exact coefficientCheck0912
  · exact coefficientCheck0913
  · exact coefficientCheck0914
  · exact coefficientCheck0915
  · exact coefficientCheck0916
  · exact coefficientCheck0917
  · exact coefficientCheck0918
  · exact coefficientCheck0919
  · exact coefficientCheck0920
  · exact coefficientCheck0921
  · exact coefficientCheck0922
  · exact coefficientCheck0923
  · exact coefficientCheck0924
  · exact coefficientCheck0925
  · exact coefficientCheck0926
  · exact coefficientCheck0927
  · exact coefficientCheck0928
  · exact coefficientCheck0929
  · exact coefficientCheck0930
  · exact coefficientCheck0931
  · exact coefficientCheck0932
  · exact coefficientCheck0933
  · exact coefficientCheck0934
  · exact coefficientCheck0935
  · exact coefficientCheck0936
  · exact coefficientCheck0937
  · exact coefficientCheck0938
  · exact coefficientCheck0939
  · exact coefficientCheck0940
  · exact coefficientCheck0941
  · exact coefficientCheck0942
  · exact coefficientCheck0943
  · exact coefficientCheck0944
  · exact coefficientCheck0945
  · exact coefficientCheck0946
  · exact coefficientCheck0947
  · exact coefficientCheck0948
  · exact coefficientCheck0949
  · exact coefficientCheck0950
  · exact coefficientCheck0951
  · exact coefficientCheck0952
  · exact coefficientCheck0953
  · exact coefficientCheck0954
  · exact coefficientCheck0955
  · exact coefficientCheck0956
  · exact coefficientCheck0957
  · exact coefficientCheck0958
  · exact coefficientCheck0959

end
end ErdosOverlap.Native6Grid
