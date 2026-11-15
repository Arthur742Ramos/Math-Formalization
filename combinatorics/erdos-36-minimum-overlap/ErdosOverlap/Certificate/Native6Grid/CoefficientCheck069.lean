module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck069
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0552 :
    completeCoefficientRowCheck factorRow row0552 552 coefficients0552 = true := by
  have hlen : coefficients0552.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0552 oddDots0552
      641 552 0 coefficients0552 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0552_checked oddSum0552_checked hlen hs

theorem coefficientCheck0553 :
    completeCoefficientRowCheck factorRow row0553 553 coefficients0553 = true := by
  have hlen : coefficients0553.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0553 oddDots0553
      641 553 0 coefficients0553 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0553_checked oddSum0553_checked hlen hs

theorem coefficientCheck0554 :
    completeCoefficientRowCheck factorRow row0554 554 coefficients0554 = true := by
  have hlen : coefficients0554.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0554 oddDots0554
      641 554 0 coefficients0554 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0554_checked oddSum0554_checked hlen hs

theorem coefficientCheck0555 :
    completeCoefficientRowCheck factorRow row0555 555 coefficients0555 = true := by
  have hlen : coefficients0555.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0555 oddDots0555
      641 555 0 coefficients0555 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0555_checked oddSum0555_checked hlen hs

theorem coefficientCheck0556 :
    completeCoefficientRowCheck factorRow row0556 556 coefficients0556 = true := by
  have hlen : coefficients0556.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0556 oddDots0556
      641 556 0 coefficients0556 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0556_checked oddSum0556_checked hlen hs

theorem coefficientCheck0557 :
    completeCoefficientRowCheck factorRow row0557 557 coefficients0557 = true := by
  have hlen : coefficients0557.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0557 oddDots0557
      641 557 0 coefficients0557 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0557_checked oddSum0557_checked hlen hs

theorem coefficientCheck0558 :
    completeCoefficientRowCheck factorRow row0558 558 coefficients0558 = true := by
  have hlen : coefficients0558.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0558 oddDots0558
      641 558 0 coefficients0558 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0558_checked oddSum0558_checked hlen hs

theorem coefficientCheck0559 :
    completeCoefficientRowCheck factorRow row0559 559 coefficients0559 = true := by
  have hlen : coefficients0559.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0559 oddDots0559
      641 559 0 coefficients0559 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0559_checked oddSum0559_checked hlen hs


end
end ErdosOverlap.Native6Grid
