module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck067
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0536 :
    completeCoefficientRowCheck factorRow row0536 536 coefficients0536 = true := by
  have hlen : coefficients0536.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0536 oddDots0536
      641 536 0 coefficients0536 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0536_checked oddSum0536_checked hlen hs

theorem coefficientCheck0537 :
    completeCoefficientRowCheck factorRow row0537 537 coefficients0537 = true := by
  have hlen : coefficients0537.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0537 oddDots0537
      641 537 0 coefficients0537 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0537_checked oddSum0537_checked hlen hs

theorem coefficientCheck0538 :
    completeCoefficientRowCheck factorRow row0538 538 coefficients0538 = true := by
  have hlen : coefficients0538.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0538 oddDots0538
      641 538 0 coefficients0538 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0538_checked oddSum0538_checked hlen hs

theorem coefficientCheck0539 :
    completeCoefficientRowCheck factorRow row0539 539 coefficients0539 = true := by
  have hlen : coefficients0539.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0539 oddDots0539
      641 539 0 coefficients0539 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0539_checked oddSum0539_checked hlen hs

theorem coefficientCheck0540 :
    completeCoefficientRowCheck factorRow row0540 540 coefficients0540 = true := by
  have hlen : coefficients0540.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0540 oddDots0540
      641 540 0 coefficients0540 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0540_checked oddSum0540_checked hlen hs

theorem coefficientCheck0541 :
    completeCoefficientRowCheck factorRow row0541 541 coefficients0541 = true := by
  have hlen : coefficients0541.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0541 oddDots0541
      641 541 0 coefficients0541 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0541_checked oddSum0541_checked hlen hs

theorem coefficientCheck0542 :
    completeCoefficientRowCheck factorRow row0542 542 coefficients0542 = true := by
  have hlen : coefficients0542.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0542 oddDots0542
      641 542 0 coefficients0542 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0542_checked oddSum0542_checked hlen hs

theorem coefficientCheck0543 :
    completeCoefficientRowCheck factorRow row0543 543 coefficients0543 = true := by
  have hlen : coefficients0543.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0543 oddDots0543
      641 543 0 coefficients0543 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0543_checked oddSum0543_checked hlen hs


end
end ErdosOverlap.Native6Grid
