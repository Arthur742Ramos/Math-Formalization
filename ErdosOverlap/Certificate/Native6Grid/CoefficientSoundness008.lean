/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck064
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck065
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck066
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck067
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck068
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck069
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck070
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck071

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk008 (j : ℕ) (hlo : 512 ≤ j) (hhi : j < 576) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0512
  · exact coefficientCheck0513
  · exact coefficientCheck0514
  · exact coefficientCheck0515
  · exact coefficientCheck0516
  · exact coefficientCheck0517
  · exact coefficientCheck0518
  · exact coefficientCheck0519
  · exact coefficientCheck0520
  · exact coefficientCheck0521
  · exact coefficientCheck0522
  · exact coefficientCheck0523
  · exact coefficientCheck0524
  · exact coefficientCheck0525
  · exact coefficientCheck0526
  · exact coefficientCheck0527
  · exact coefficientCheck0528
  · exact coefficientCheck0529
  · exact coefficientCheck0530
  · exact coefficientCheck0531
  · exact coefficientCheck0532
  · exact coefficientCheck0533
  · exact coefficientCheck0534
  · exact coefficientCheck0535
  · exact coefficientCheck0536
  · exact coefficientCheck0537
  · exact coefficientCheck0538
  · exact coefficientCheck0539
  · exact coefficientCheck0540
  · exact coefficientCheck0541
  · exact coefficientCheck0542
  · exact coefficientCheck0543
  · exact coefficientCheck0544
  · exact coefficientCheck0545
  · exact coefficientCheck0546
  · exact coefficientCheck0547
  · exact coefficientCheck0548
  · exact coefficientCheck0549
  · exact coefficientCheck0550
  · exact coefficientCheck0551
  · exact coefficientCheck0552
  · exact coefficientCheck0553
  · exact coefficientCheck0554
  · exact coefficientCheck0555
  · exact coefficientCheck0556
  · exact coefficientCheck0557
  · exact coefficientCheck0558
  · exact coefficientCheck0559
  · exact coefficientCheck0560
  · exact coefficientCheck0561
  · exact coefficientCheck0562
  · exact coefficientCheck0563
  · exact coefficientCheck0564
  · exact coefficientCheck0565
  · exact coefficientCheck0566
  · exact coefficientCheck0567
  · exact coefficientCheck0568
  · exact coefficientCheck0569
  · exact coefficientCheck0570
  · exact coefficientCheck0571
  · exact coefficientCheck0572
  · exact coefficientCheck0573
  · exact coefficientCheck0574
  · exact coefficientCheck0575

end
end ErdosOverlap.Native6Grid
