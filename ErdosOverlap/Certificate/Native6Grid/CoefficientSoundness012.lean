/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck096
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck097
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck098
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck099
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck100
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck101
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck102
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck103

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk012 (j : ℕ) (hlo : 768 ≤ j) (hhi : j < 832) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0768
  · exact coefficientCheck0769
  · exact coefficientCheck0770
  · exact coefficientCheck0771
  · exact coefficientCheck0772
  · exact coefficientCheck0773
  · exact coefficientCheck0774
  · exact coefficientCheck0775
  · exact coefficientCheck0776
  · exact coefficientCheck0777
  · exact coefficientCheck0778
  · exact coefficientCheck0779
  · exact coefficientCheck0780
  · exact coefficientCheck0781
  · exact coefficientCheck0782
  · exact coefficientCheck0783
  · exact coefficientCheck0784
  · exact coefficientCheck0785
  · exact coefficientCheck0786
  · exact coefficientCheck0787
  · exact coefficientCheck0788
  · exact coefficientCheck0789
  · exact coefficientCheck0790
  · exact coefficientCheck0791
  · exact coefficientCheck0792
  · exact coefficientCheck0793
  · exact coefficientCheck0794
  · exact coefficientCheck0795
  · exact coefficientCheck0796
  · exact coefficientCheck0797
  · exact coefficientCheck0798
  · exact coefficientCheck0799
  · exact coefficientCheck0800
  · exact coefficientCheck0801
  · exact coefficientCheck0802
  · exact coefficientCheck0803
  · exact coefficientCheck0804
  · exact coefficientCheck0805
  · exact coefficientCheck0806
  · exact coefficientCheck0807
  · exact coefficientCheck0808
  · exact coefficientCheck0809
  · exact coefficientCheck0810
  · exact coefficientCheck0811
  · exact coefficientCheck0812
  · exact coefficientCheck0813
  · exact coefficientCheck0814
  · exact coefficientCheck0815
  · exact coefficientCheck0816
  · exact coefficientCheck0817
  · exact coefficientCheck0818
  · exact coefficientCheck0819
  · exact coefficientCheck0820
  · exact coefficientCheck0821
  · exact coefficientCheck0822
  · exact coefficientCheck0823
  · exact coefficientCheck0824
  · exact coefficientCheck0825
  · exact coefficientCheck0826
  · exact coefficientCheck0827
  · exact coefficientCheck0828
  · exact coefficientCheck0829
  · exact coefficientCheck0830
  · exact coefficientCheck0831

end
end ErdosOverlap.Native6Grid
