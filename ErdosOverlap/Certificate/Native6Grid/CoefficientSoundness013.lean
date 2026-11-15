/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck104
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck105
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck106
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck107
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck108
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck109
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck110
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck111

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk013 (j : ℕ) (hlo : 832 ≤ j) (hhi : j < 896) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0832
  · exact coefficientCheck0833
  · exact coefficientCheck0834
  · exact coefficientCheck0835
  · exact coefficientCheck0836
  · exact coefficientCheck0837
  · exact coefficientCheck0838
  · exact coefficientCheck0839
  · exact coefficientCheck0840
  · exact coefficientCheck0841
  · exact coefficientCheck0842
  · exact coefficientCheck0843
  · exact coefficientCheck0844
  · exact coefficientCheck0845
  · exact coefficientCheck0846
  · exact coefficientCheck0847
  · exact coefficientCheck0848
  · exact coefficientCheck0849
  · exact coefficientCheck0850
  · exact coefficientCheck0851
  · exact coefficientCheck0852
  · exact coefficientCheck0853
  · exact coefficientCheck0854
  · exact coefficientCheck0855
  · exact coefficientCheck0856
  · exact coefficientCheck0857
  · exact coefficientCheck0858
  · exact coefficientCheck0859
  · exact coefficientCheck0860
  · exact coefficientCheck0861
  · exact coefficientCheck0862
  · exact coefficientCheck0863
  · exact coefficientCheck0864
  · exact coefficientCheck0865
  · exact coefficientCheck0866
  · exact coefficientCheck0867
  · exact coefficientCheck0868
  · exact coefficientCheck0869
  · exact coefficientCheck0870
  · exact coefficientCheck0871
  · exact coefficientCheck0872
  · exact coefficientCheck0873
  · exact coefficientCheck0874
  · exact coefficientCheck0875
  · exact coefficientCheck0876
  · exact coefficientCheck0877
  · exact coefficientCheck0878
  · exact coefficientCheck0879
  · exact coefficientCheck0880
  · exact coefficientCheck0881
  · exact coefficientCheck0882
  · exact coefficientCheck0883
  · exact coefficientCheck0884
  · exact coefficientCheck0885
  · exact coefficientCheck0886
  · exact coefficientCheck0887
  · exact coefficientCheck0888
  · exact coefficientCheck0889
  · exact coefficientCheck0890
  · exact coefficientCheck0891
  · exact coefficientCheck0892
  · exact coefficientCheck0893
  · exact coefficientCheck0894
  · exact coefficientCheck0895

end
end ErdosOverlap.Native6Grid
