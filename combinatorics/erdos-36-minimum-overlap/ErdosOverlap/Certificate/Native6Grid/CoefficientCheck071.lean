module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck071
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0568 :
    completeCoefficientRowCheck factorRow row0568 568 coefficients0568 = true := by
  have hlen : coefficients0568.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0568 oddDots0568
      641 568 0 coefficients0568 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0568_checked oddSum0568_checked hlen hs

theorem coefficientCheck0569 :
    completeCoefficientRowCheck factorRow row0569 569 coefficients0569 = true := by
  have hlen : coefficients0569.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0569 oddDots0569
      641 569 0 coefficients0569 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0569_checked oddSum0569_checked hlen hs

theorem coefficientCheck0570 :
    completeCoefficientRowCheck factorRow row0570 570 coefficients0570 = true := by
  have hlen : coefficients0570.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0570 oddDots0570
      641 570 0 coefficients0570 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0570_checked oddSum0570_checked hlen hs

theorem coefficientCheck0571 :
    completeCoefficientRowCheck factorRow row0571 571 coefficients0571 = true := by
  have hlen : coefficients0571.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0571 oddDots0571
      641 571 0 coefficients0571 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0571_checked oddSum0571_checked hlen hs

theorem coefficientCheck0572 :
    completeCoefficientRowCheck factorRow row0572 572 coefficients0572 = true := by
  have hlen : coefficients0572.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0572 oddDots0572
      641 572 0 coefficients0572 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0572_checked oddSum0572_checked hlen hs

theorem coefficientCheck0573 :
    completeCoefficientRowCheck factorRow row0573 573 coefficients0573 = true := by
  have hlen : coefficients0573.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0573 oddDots0573
      641 573 0 coefficients0573 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0573_checked oddSum0573_checked hlen hs

theorem coefficientCheck0574 :
    completeCoefficientRowCheck factorRow row0574 574 coefficients0574 = true := by
  have hlen : coefficients0574.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0574 oddDots0574
      641 574 0 coefficients0574 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0574_checked oddSum0574_checked hlen hs

theorem coefficientCheck0575 :
    completeCoefficientRowCheck factorRow row0575 575 coefficients0575 = true := by
  have hlen : coefficients0575.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0575 oddDots0575
      641 575 0 coefficients0575 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0575_checked oddSum0575_checked hlen hs


end
end ErdosOverlap.Native6Grid
