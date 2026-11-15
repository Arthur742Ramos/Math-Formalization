/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck072
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck073
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck074
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck075
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck076
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck077
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck078
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck079

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk009 (j : ℕ) (hlo : 576 ≤ j) (hhi : j < 640) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0576
  · exact coefficientCheck0577
  · exact coefficientCheck0578
  · exact coefficientCheck0579
  · exact coefficientCheck0580
  · exact coefficientCheck0581
  · exact coefficientCheck0582
  · exact coefficientCheck0583
  · exact coefficientCheck0584
  · exact coefficientCheck0585
  · exact coefficientCheck0586
  · exact coefficientCheck0587
  · exact coefficientCheck0588
  · exact coefficientCheck0589
  · exact coefficientCheck0590
  · exact coefficientCheck0591
  · exact coefficientCheck0592
  · exact coefficientCheck0593
  · exact coefficientCheck0594
  · exact coefficientCheck0595
  · exact coefficientCheck0596
  · exact coefficientCheck0597
  · exact coefficientCheck0598
  · exact coefficientCheck0599
  · exact coefficientCheck0600
  · exact coefficientCheck0601
  · exact coefficientCheck0602
  · exact coefficientCheck0603
  · exact coefficientCheck0604
  · exact coefficientCheck0605
  · exact coefficientCheck0606
  · exact coefficientCheck0607
  · exact coefficientCheck0608
  · exact coefficientCheck0609
  · exact coefficientCheck0610
  · exact coefficientCheck0611
  · exact coefficientCheck0612
  · exact coefficientCheck0613
  · exact coefficientCheck0614
  · exact coefficientCheck0615
  · exact coefficientCheck0616
  · exact coefficientCheck0617
  · exact coefficientCheck0618
  · exact coefficientCheck0619
  · exact coefficientCheck0620
  · exact coefficientCheck0621
  · exact coefficientCheck0622
  · exact coefficientCheck0623
  · exact coefficientCheck0624
  · exact coefficientCheck0625
  · exact coefficientCheck0626
  · exact coefficientCheck0627
  · exact coefficientCheck0628
  · exact coefficientCheck0629
  · exact coefficientCheck0630
  · exact coefficientCheck0631
  · exact coefficientCheck0632
  · exact coefficientCheck0633
  · exact coefficientCheck0634
  · exact coefficientCheck0635
  · exact coefficientCheck0636
  · exact coefficientCheck0637
  · exact coefficientCheck0638
  · exact coefficientCheck0639

end
end ErdosOverlap.Native6Grid
