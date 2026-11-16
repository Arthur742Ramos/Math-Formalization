/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck080
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck081
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck082
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck083
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck084
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck085
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck086
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck087

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk010 (j : ℕ) (hlo : 640 ≤ j) (hhi : j < 704) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0640
  · exact coefficientCheck0641
  · exact coefficientCheck0642
  · exact coefficientCheck0643
  · exact coefficientCheck0644
  · exact coefficientCheck0645
  · exact coefficientCheck0646
  · exact coefficientCheck0647
  · exact coefficientCheck0648
  · exact coefficientCheck0649
  · exact coefficientCheck0650
  · exact coefficientCheck0651
  · exact coefficientCheck0652
  · exact coefficientCheck0653
  · exact coefficientCheck0654
  · exact coefficientCheck0655
  · exact coefficientCheck0656
  · exact coefficientCheck0657
  · exact coefficientCheck0658
  · exact coefficientCheck0659
  · exact coefficientCheck0660
  · exact coefficientCheck0661
  · exact coefficientCheck0662
  · exact coefficientCheck0663
  · exact coefficientCheck0664
  · exact coefficientCheck0665
  · exact coefficientCheck0666
  · exact coefficientCheck0667
  · exact coefficientCheck0668
  · exact coefficientCheck0669
  · exact coefficientCheck0670
  · exact coefficientCheck0671
  · exact coefficientCheck0672
  · exact coefficientCheck0673
  · exact coefficientCheck0674
  · exact coefficientCheck0675
  · exact coefficientCheck0676
  · exact coefficientCheck0677
  · exact coefficientCheck0678
  · exact coefficientCheck0679
  · exact coefficientCheck0680
  · exact coefficientCheck0681
  · exact coefficientCheck0682
  · exact coefficientCheck0683
  · exact coefficientCheck0684
  · exact coefficientCheck0685
  · exact coefficientCheck0686
  · exact coefficientCheck0687
  · exact coefficientCheck0688
  · exact coefficientCheck0689
  · exact coefficientCheck0690
  · exact coefficientCheck0691
  · exact coefficientCheck0692
  · exact coefficientCheck0693
  · exact coefficientCheck0694
  · exact coefficientCheck0695
  · exact coefficientCheck0696
  · exact coefficientCheck0697
  · exact coefficientCheck0698
  · exact coefficientCheck0699
  · exact coefficientCheck0700
  · exact coefficientCheck0701
  · exact coefficientCheck0702
  · exact coefficientCheck0703

end
end ErdosOverlap.Native6Grid
