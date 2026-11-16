/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck088
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck089
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck090
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck091
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck092
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck093
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck094
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck095

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk011 (j : ℕ) (hlo : 704 ≤ j) (hhi : j < 768) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0704
  · exact coefficientCheck0705
  · exact coefficientCheck0706
  · exact coefficientCheck0707
  · exact coefficientCheck0708
  · exact coefficientCheck0709
  · exact coefficientCheck0710
  · exact coefficientCheck0711
  · exact coefficientCheck0712
  · exact coefficientCheck0713
  · exact coefficientCheck0714
  · exact coefficientCheck0715
  · exact coefficientCheck0716
  · exact coefficientCheck0717
  · exact coefficientCheck0718
  · exact coefficientCheck0719
  · exact coefficientCheck0720
  · exact coefficientCheck0721
  · exact coefficientCheck0722
  · exact coefficientCheck0723
  · exact coefficientCheck0724
  · exact coefficientCheck0725
  · exact coefficientCheck0726
  · exact coefficientCheck0727
  · exact coefficientCheck0728
  · exact coefficientCheck0729
  · exact coefficientCheck0730
  · exact coefficientCheck0731
  · exact coefficientCheck0732
  · exact coefficientCheck0733
  · exact coefficientCheck0734
  · exact coefficientCheck0735
  · exact coefficientCheck0736
  · exact coefficientCheck0737
  · exact coefficientCheck0738
  · exact coefficientCheck0739
  · exact coefficientCheck0740
  · exact coefficientCheck0741
  · exact coefficientCheck0742
  · exact coefficientCheck0743
  · exact coefficientCheck0744
  · exact coefficientCheck0745
  · exact coefficientCheck0746
  · exact coefficientCheck0747
  · exact coefficientCheck0748
  · exact coefficientCheck0749
  · exact coefficientCheck0750
  · exact coefficientCheck0751
  · exact coefficientCheck0752
  · exact coefficientCheck0753
  · exact coefficientCheck0754
  · exact coefficientCheck0755
  · exact coefficientCheck0756
  · exact coefficientCheck0757
  · exact coefficientCheck0758
  · exact coefficientCheck0759
  · exact coefficientCheck0760
  · exact coefficientCheck0761
  · exact coefficientCheck0762
  · exact coefficientCheck0763
  · exact coefficientCheck0764
  · exact coefficientCheck0765
  · exact coefficientCheck0766
  · exact coefficientCheck0767

end
end ErdosOverlap.Native6Grid
